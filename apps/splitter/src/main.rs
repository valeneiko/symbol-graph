use std::{
    cell::RefCell,
    io::{Read as _, Write},
    path::{Path, PathBuf},
    rc::{Rc, Weak},
    sync::{Arc, Condvar, Mutex, OnceLock},
    time::Instant,
};

use oxc::span::CompactStr;
use oxc_ecmascript::BoundNames;
use rustc_hash::FxHashMap;

const THREADS: u8 = 24;

#[derive(Debug)]
enum Error {
    UnknownExtension(oxc::span::UnknownExtension),
    Parser(Vec<oxc::diagnostics::OxcDiagnostic>),
    Semantic(Vec<oxc::diagnostics::OxcDiagnostic>),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::UnknownExtension(err) => err.fmt(f),
            Error::Semantic(vec) | Error::Parser(vec) => {
                let reporter = oxc::diagnostics::GraphicalReportHandler::new();
                for err in vec {
                    reporter.render_report(f, err)?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for Error {}

impl From<oxc::span::UnknownExtension> for Error {
    fn from(value: oxc::span::UnknownExtension) -> Self {
        Self::UnknownExtension(value)
    }
}

struct LinterModuleRecord<'a> {
    pub module_record: oxc::syntax::module_record::ModuleRecord<'a>,
    pub resolved_absolute_path: PathBuf,
    pub loaded_modules: FxHashMap<oxc::span::Atom<'a>, Weak<RefCell<LinterModuleRecord<'a>>>>,
    exported_bindings_from_star_export: OnceLock<FxHashMap<PathBuf, Vec<CompactStr>>>,
    pub export_default: Option<oxc::span::Span>,
}

impl LinterModuleRecord<'_> {
    pub(crate) fn exported_bindings_from_star_exports(
        &self,
    ) -> &FxHashMap<PathBuf, Vec<CompactStr>> {
        self.exported_bindings_from_star_export.get_or_init(|| {
            let mut exported_bindings_from_star_export: FxHashMap<PathBuf, Vec<CompactStr>> =
                FxHashMap::default();
            for export_entry in &self.module_record.star_export_entries {
                let Some(module_request) = &export_entry.module_request else {
                    continue;
                };
                let Some(remote_module_record) = self.loaded_modules.get(&module_request.name)
                else {
                    continue;
                };
                let remote_module_record = remote_module_record.upgrade().unwrap();
                let remote_module_record = remote_module_record.borrow();
                // Append both remote `bindings` and `exported_bindings_from_star_export`

                let remote_exported_bindings_from_star_export = remote_module_record
                    .exported_bindings_from_star_exports()
                    .iter()
                    .flat_map(|(_, value)| value.clone());
                let remote_bindings = remote_module_record
                    .module_record
                    .exported_bindings
                    .keys()
                    .map(|k| k.to_compact_str())
                    .chain(remote_exported_bindings_from_star_export);
                exported_bindings_from_star_export
                    .entry(remote_module_record.resolved_absolute_path.clone())
                    .or_default()
                    .extend(remote_bindings);
            }
            exported_bindings_from_star_export
        })
    }
}

impl std::fmt::Debug for LinterModuleRecord<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // recursively formatting loaded modules can crash when the module graph is cyclic
        let loaded_modules = self
            .loaded_modules
            .keys()
            .map(ToString::to_string)
            .reduce(|acc, key| format!("{acc}, {key}"))
            .unwrap_or_default();
        let loaded_modules = format!("{{ {loaded_modules} }}");
        f.debug_struct("ModuleRecord")
            .field("has_module_syntax", &self.module_record.has_module_syntax)
            .field("resolved_absolute_path", &self.resolved_absolute_path)
            .field("requested_modules", &self.module_record.requested_modules)
            .field("loaded_modules", &loaded_modules)
            .field("import_entries", &self.module_record.import_entries)
            .field("local_export_entries", &self.module_record.local_export_entries)
            .field("indirect_export_entries", &self.module_record.indirect_export_entries)
            .field("star_export_entries", &self.module_record.star_export_entries)
            .field("exported_bindings", &self.module_record.exported_bindings)
            .field("exported_bindings_from_star_export", &self.exported_bindings_from_star_export)
            .field("export_default", &self.export_default)
            .finish()
    }
}

oxc_index::define_index_type! {
  pub struct ModuleId = u32;
}

oxc_index::define_index_type! {
  pub struct NameId = u32;
}

oxc_index::define_index_type! {
  pub struct UniqueSymbolId = u32;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct GlobalSymbolId {
    module: ModuleId,
    name: NameId,
}

struct SymbolReferences {
    next_name_id: NameId,
    names: rustc_hash::FxHashMap<oxc::span::CompactStr, NameId>,
    references: rustc_hash::FxHashMap<GlobalSymbolId, Vec<GlobalSymbolId>>,
}

impl Default for SymbolReferences {
    fn default() -> Self {
        Self {
            next_name_id: NameId::from_raw(0),
            names: rustc_hash::FxHashMap::default(),
            references: rustc_hash::FxHashMap::default(),
        }
    }
}

impl SymbolReferences {
    fn get_name_id(&mut self, name: &str) -> NameId {
        match self.names.entry(name.into()) {
            std::collections::hash_map::Entry::Occupied(e) => *e.get(),
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(self.next_name_id);
                let result = self.next_name_id;
                self.next_name_id += 1;

                result
            }
        }
    }

    fn add_symbol_reference(&mut self, from: GlobalSymbolId, to: GlobalSymbolId) {
        match self.references.entry(from) {
            std::collections::hash_map::Entry::Occupied(mut e) => {
                e.get_mut().push(to);
            }
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(vec![to]);
            }
        }
    }

    fn extend(&mut self, other: &Self) -> &mut Self {
        let mut name_mapping =
            oxc_index::IndexVec::<NameId, NameId>::with_capacity(other.names.len());
        name_mapping.resize(other.names.len(), NameId::from_raw(0));
        for (other_name, &other_id) in &other.names {
            let id = self.get_name_id(other_name);
            name_mapping[other_id] = id;
        }

        for (&from, to) in &other.references {
            let from_new_name = name_mapping[from.name];
            let to_target = match self
                .references
                .entry(GlobalSymbolId { module: from.module, name: from_new_name })
            {
                std::collections::hash_map::Entry::Occupied(e) => {
                    let to = e.into_mut();
                    to.reserve(to.len());
                    to
                }
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(Vec::with_capacity(to.len()))
                }
            };

            for &to in to {
                let to_new_name = name_mapping[to.name];
                to_target.push(GlobalSymbolId { module: to.module, name: to_new_name });
            }
        }

        self
    }
}

#[derive(Default)]
struct ThreadData<'a> {
    semantic: rustc_hash::FxHashMap<
        ModuleId,
        (oxc::semantic::Semantic<'a>, Rc<RefCell<LinterModuleRecord<'a>>>),
    >,
    references: SymbolReferences,
}

#[expect(unsafe_code)]
// SAFETY: must use the allocator passed beside this.
unsafe impl Send for ThreadData<'_> {}

fn parse_file<'a>(
    alloc: &'a oxc::allocator::Allocator,
    source_path: &'_ std::path::Path,
    source_text: &'a str,
) -> Result<(oxc::semantic::Semantic<'a>, oxc::syntax::module_record::ModuleRecord<'a>), Error> {
    let source_type = oxc::span::SourceType::from_path(source_path)?;
    let parser = oxc::parser::Parser::new(alloc, source_text, source_type);

    let parse_result = parser.parse();
    if !parse_result.errors.is_empty() {
        return Err(Error::Parser(parse_result.errors));
    }

    let program = alloc.alloc(parse_result.program);
    let builder = oxc::semantic::SemanticBuilder::new()
        // Enable additional syntax checks not performed by the parser
        .with_check_syntax_error(true);

    let semantic_result = builder.build(program);
    let mut module_record_mut = parse_result.module_record;

    if !semantic_result.errors.is_empty() {
        return Err(Error::Semantic(semantic_result.errors));
    }

    // Add exported TS declarations to module record
    let semantic = semantic_result.semantic;
    let nodes = semantic.nodes();
    let scope_tree = semantic.scoping();
    // let symbol_table = semantic.symbol_table();
    let root_scope = scope_tree.root_scope_id();
    for symbol in scope_tree.iter_bindings_in(root_scope) {
        let flags = scope_tree.symbol_flags(symbol);
        if flags.is_value() || flags.is_import() || !flags.is_type() {
            continue;
        }

        let decl = scope_tree.symbol_declaration(symbol);
        let (name_span, decl_span) = match nodes.get_node(decl).kind() {
            oxc::ast::AstKind::TSTypeAliasDeclaration(decl) => {
                let id = &decl.id;
                (oxc::syntax::module_record::NameSpan::new(id.name, id.span), decl.span)
            }
            oxc::ast::AstKind::TSInterfaceDeclaration(decl) => {
                let id = &decl.id;
                (oxc::syntax::module_record::NameSpan::new(id.name, id.span), decl.span)
            }
            node => panic!("unexpected node kind: {:?}", node.debug_name()),
        };

        match module_record_mut.exported_bindings.entry(name_span.name) {
            oxc::allocator::hash_map::Entry::Occupied(_) => {}
            oxc::allocator::hash_map::Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(name_span.span);
            }
        }

        module_record_mut.local_export_entries.push(oxc::syntax::module_record::ExportEntry {
            span: scope_tree.symbol_span(symbol),
            module_request: None,
            import_name: oxc::syntax::module_record::ExportImportName::Null,
            export_name: oxc::syntax::module_record::ExportExportName::Name(name_span.clone()),
            local_name: oxc::syntax::module_record::ExportLocalName::Name(name_span),
            is_type: false,
            statement_span: decl_span,
        });
    }

    // Add TypeScript and CJS exports to module record
    for stmt in &program.body {
        // Add export type {} from '...' to module record
        if let Some(module_decl) = stmt.as_module_declaration() {
            match module_decl {
                // oxc::ast::ast::ModuleDeclaration::ImportDeclaration(import_declaration) => todo!(),
                // oxc::ast::ast::ModuleDeclaration::ExportAllDeclaration(export_all_declaration) => todo!(),
                // oxc::ast::ast::ModuleDeclaration::ExportDefaultDeclaration(export_default_declaration) => todo!(),
                // oxc::ast::ast::ModuleDeclaration::TSExportAssignment(tsexport_assignment) => todo!(),
                // oxc::ast::ast::ModuleDeclaration::TSNamespaceExportDeclaration(tsnamespace_export_declaration) => todo!(),
                oxc::ast::ast::ModuleDeclaration::ExportNamedDeclaration(decl)
                    if decl.export_kind.is_type() =>
                {
                    let module_request = decl.source.as_ref().map(|source| {
                        oxc::syntax::module_record::NameSpan::new(source.value, source.span)
                    });

                    if let Some(module_request) = &module_request {
                        let requested_module = oxc::syntax::module_record::RequestedModule {
                            statement_span: decl.span,
                            span: module_request.span,
                            is_type: true,
                            is_import: false,
                        };

                        match module_record_mut.requested_modules.entry(module_request.name) {
                            oxc::allocator::hash_map::Entry::Occupied(mut occupied_entry) => {
                                occupied_entry.get_mut().push(requested_module);
                            }
                            oxc::allocator::hash_map::Entry::Vacant(vacant_entry) => {
                                let mut vec = oxc::allocator::Vec::new_in(alloc);
                                vec.push(requested_module);
                                vacant_entry.insert(vec);
                            }
                        }
                    }

                    if let Some(decl) = &decl.declaration {
                        decl.bound_names(&mut |ident| {
                            let export_name = oxc::syntax::module_record::ExportExportName::Name(
                                oxc::syntax::module_record::NameSpan::new(ident.name, ident.span),
                            );
                            let local_name = oxc::syntax::module_record::ExportLocalName::Name(
                                oxc::syntax::module_record::NameSpan::new(ident.name, ident.span),
                            );
                            let export_entry = oxc::syntax::module_record::ExportEntry {
                                statement_span: oxc::span::GetSpan::span(decl),
                                span: oxc::span::GetSpan::span(decl),
                                module_request: module_request.clone(),
                                import_name: oxc::syntax::module_record::ExportImportName::Null,
                                export_name,
                                local_name,
                                is_type: true,
                            };
                            module_record_mut.local_export_entries.push(export_entry);
                            match module_record_mut.exported_bindings.entry(ident.name) {
                                oxc::allocator::hash_map::Entry::Occupied(_) => {}
                                oxc::allocator::hash_map::Entry::Vacant(vacant_entry) => {
                                    vacant_entry.insert(ident.span);
                                }
                            }
                        });
                    }

                    for specifier in &decl.specifiers {
                        let export_name = oxc::syntax::module_record::ExportExportName::Name(
                            oxc::syntax::module_record::NameSpan::new(
                                specifier.exported.name(),
                                oxc::span::GetSpan::span(&specifier.exported),
                            ),
                        );
                        let import_name = if module_request.is_some() {
                            oxc::syntax::module_record::ExportImportName::Name(
                                oxc::syntax::module_record::NameSpan::new(
                                    specifier.local.name(),
                                    oxc::span::GetSpan::span(&specifier.local),
                                ),
                            )
                        } else {
                            oxc::syntax::module_record::ExportImportName::Null
                        };
                        let local_name = if module_request.is_some() {
                            oxc::syntax::module_record::ExportLocalName::Null
                        } else {
                            oxc::syntax::module_record::ExportLocalName::Name(
                                oxc::syntax::module_record::NameSpan::new(
                                    specifier.local.name(),
                                    oxc::span::GetSpan::span(&specifier.local),
                                ),
                            )
                        };
                        let export_entry = oxc::syntax::module_record::ExportEntry {
                            statement_span: decl.span,
                            span: specifier.span,
                            module_request: module_request.clone(),
                            import_name,
                            export_name,
                            local_name,
                            is_type: true,
                        };
                        module_record_mut.indirect_export_entries.push(export_entry);
                        match module_record_mut.exported_bindings.entry(specifier.exported.name()) {
                            oxc::allocator::hash_map::Entry::Occupied(_) => {}
                            oxc::allocator::hash_map::Entry::Vacant(vacant_entry) => {
                                vacant_entry.insert(oxc::span::GetSpan::span(&specifier.exported));
                            }
                        }
                    }
                }
                _ => {}
            }
        } else if let oxc::ast::ast::Statement::ExpressionStatement(stmt) = &stmt {
            match &stmt.expression {
                oxc::ast::ast::Expression::AssignmentExpression(expr)
                    if expr.operator == oxc::ast::ast::AssignmentOperator::Assign =>
                {
                    let oxc::ast::ast::AssignmentTarget::StaticMemberExpression(left) = &expr.left
                    else {
                        continue;
                    };

                    let oxc::ast::ast::Expression::Identifier(ident) = &left.object else {
                        continue;
                    };

                    match ident.name.as_str() {
                        // exports.foo = ...
                        "exports" => {
                            let name_span = oxc::syntax::module_record::NameSpan::new(
                                left.property.name,
                                left.property.span,
                            );
                            let export_entry = oxc::syntax::module_record::ExportEntry {
                                export_name: oxc::syntax::module_record::ExportExportName::Name(
                                    name_span.clone(),
                                ),
                                span: expr.span,
                                ..Default::default()
                            };
                            module_record_mut.local_export_entries.push(export_entry);
                            match module_record_mut.exported_bindings.entry(name_span.name) {
                                oxc::allocator::hash_map::Entry::Occupied(_) => {}
                                oxc::allocator::hash_map::Entry::Vacant(vacant_entry) => {
                                    vacant_entry.insert(name_span.span);
                                }
                            }
                        }
                        // module.exports = { foo: ... }
                        "module" if left.property.name == "exports" => {
                            let oxc::ast::ast::Expression::ObjectExpression(expr) = &expr.right
                            else {
                                continue;
                            };

                            for prop in &expr.properties {
                                let oxc::ast::ast::ObjectPropertyKind::ObjectProperty(prop) = prop
                                else {
                                    continue;
                                };

                                let oxc::ast::ast::PropertyKey::StaticIdentifier(ident) = &prop.key
                                else {
                                    continue;
                                };

                                let name_span = oxc::syntax::module_record::NameSpan::new(
                                    ident.name, ident.span,
                                );
                                let export_entry = oxc::syntax::module_record::ExportEntry {
                                    export_name: oxc::syntax::module_record::ExportExportName::Name(
                                        name_span.clone(),
                                    ),
                                    span: prop.span,
                                    ..Default::default()
                                };
                                module_record_mut.local_export_entries.push(export_entry);
                                match module_record_mut.exported_bindings.entry(name_span.name) {
                                    oxc::allocator::hash_map::Entry::Occupied(_) => {}
                                    oxc::allocator::hash_map::Entry::Vacant(vacant_entry) => {
                                        vacant_entry.insert(name_span.span);
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
    }

    Ok((semantic, module_record_mut))
}

struct WorkQueue<'a, T> {
    queue: &'a mut Vec<T>,
    workers: u8,
}

impl<'a, T> WorkQueue<'a, T> {
    fn new(init_queue: &'a mut Vec<T>) -> Self {
        Self { queue: init_queue, workers: 0 }
    }
}

fn quick_walk(path: &Path) -> impl Iterator<Item = PathBuf> {
    let mut result: [Vec<PathBuf>; THREADS as usize] = Default::default();

    let mut queue = vec![path.to_path_buf()];
    std::thread::scope(|s| {
        let queue = Arc::new((Mutex::new(WorkQueue::new(&mut queue)), Condvar::new()));

        for result in &mut result {
            let queue = Arc::clone(&queue);
            s.spawn(move || {
                let (queue, cvar) = &*queue;
                let mut working: u8 = 0;
                loop {
                    let path = {
                        let mut queue = queue.lock().unwrap();
                        loop {
                            if let Some(path) = queue.queue.pop() {
                                queue.workers += 1 - working;
                                working = 1;
                                break path;
                            }

                            queue.workers -= working;
                            working = 0;

                            if queue.workers == 0 {
                                cvar.notify_all();
                                return;
                            }
                            queue = cvar.wait(queue).unwrap();
                        }
                    };

                    let Ok(dir) = path.read_dir() else {
                        continue;
                    };
                    for entry in dir {
                        let Ok(entry) = entry else {
                            continue;
                        };

                        let path = entry.path();
                        if !path.is_dir() {
                            let ext = path.extension().unwrap_or_default();
                            if ext == "ts"
                                || ext == "js"
                                || ext == "tsx"
                                || ext == "jsx"
                                || ext == "mts"
                                || ext == "cts"
                                || ext == "mjs"
                                || ext == "cjs"
                            {
                                result.push(path);
                            }

                            continue;
                        }

                        let name = path.file_name().unwrap_or_default();
                        if name == "node_modules" || name == "typedefs" || name == "dist" {
                            continue;
                        }

                        queue.lock().unwrap().queue.push(path);
                        cvar.notify_one();
                    }
                }
            });
        }
    });

    result.into_iter().flatten()
}

#[expect(clippy::print_stdout, clippy::unnecessary_wraps)]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let Some(root_dir) = args.next() else {
        panic!("Missing path to TypeScript repo");
    };
    let Some(out_dir) = args.next() else {
        panic!("Missing path to output directory");
    };
    let root_dir = root_dir.as_str();
    let out_dir = std::path::Path::new(out_dir.as_str());

    let now = Instant::now();
    let modules = {
        let mut modules: oxc_index::IndexVec<ModuleId, PathBuf> =
            quick_walk(std::path::Path::new(root_dir)).collect();
        modules.sort();
        modules
    };
    let module_paths: rustc_hash::FxHashMap<&Path, ModuleId> =
        modules.iter_enumerated().map(|(id, path)| (path.as_path(), id)).collect();
    let module_paths = &module_paths;
    let elapsed_discovery = now.elapsed();

    let resolver = oxc_resolver::Resolver::new(oxc_resolver::ResolveOptions {
        tsconfig: Some(oxc_resolver::TsconfigDiscovery::Manual(oxc_resolver::TsconfigOptions {
            config_file: format!(r"{root_dir}\tsconfig.json").into(),
            references: oxc_resolver::TsconfigReferences::Auto,
        })),
        extensions: ["ts", "js", "tsx", "jsx", "mts", "cts", "mjs", "cjs"]
            .map(|x| format!(".{x}"))
            .to_vec(),
        condition_names: ["node", "require"].map(std::borrow::ToOwned::to_owned).to_vec(),
        builtin_modules: true,
        ..Default::default()
    });
    let resolver = &resolver;
    let iter = std::sync::Arc::new(std::sync::Mutex::new(module_paths.iter()));

    let mut alloc: [oxc::allocator::Allocator; THREADS as usize] = Default::default();
    let mut thread_data: [ThreadData; THREADS as usize] = Default::default();

    std::thread::scope(|s| {
        let mut thread_data = thread_data.iter_mut();

        for alloc in &mut alloc {
            let thread_data = thread_data.next().unwrap();
            let iter = std::sync::Arc::clone(&iter);
            s.spawn(move || {
                loop {
                    let Some((path, &module_id)) = iter.lock().unwrap().next() else {
                        return;
                    };

                    let source_text = {
                        let file = std::fs::File::open(path).unwrap();
                        let len = file.metadata().unwrap().len();
                        let len_usize = usize::try_from(len).unwrap();

                        // SAFETY: copied from oxc
                        let layout =
                            unsafe { std::alloc::Layout::from_size_align_unchecked(len_usize, 1) };
                        let ptr = alloc.alloc_layout(layout);
                        {
                            // SAFETY: copied from oxc
                            let vec = unsafe { Vec::from_raw_parts(ptr.as_ptr(), 0, len_usize) };
                            let mut vec = std::mem::ManuallyDrop::new(vec);
                            file.take(len).read_to_end(&mut vec).unwrap();
                        }
                        let bytes =
                        // SAFETY: copied from oxc
                            unsafe { std::slice::from_raw_parts(ptr.as_ptr(), len_usize) };
                        // SAFETY: copied from oxc
                        unsafe { str::from_utf8_unchecked(bytes) }
                    };

                    let parse_result = parse_file(alloc, path, source_text)
                        .expect("file to be parsed successfully");
                    let (semantic, module_record) = match thread_data.semantic.entry(module_id) {
                        std::collections::hash_map::Entry::Occupied(e) => e.into_mut(),
                        std::collections::hash_map::Entry::Vacant(e) => {
                            let export_default = parse_result
                                .1
                                .local_export_entries
                                .iter()
                                .filter_map(|export_entry| {
                                    export_entry.export_name.default_export_span()
                                })
                                .chain(parse_result.1.indirect_export_entries.iter().filter_map(
                                    |export_entry| export_entry.export_name.default_export_span(),
                                ))
                                .next();
                            e.insert((
                                parse_result.0,
                                Rc::new(RefCell::new(LinterModuleRecord {
                                    module_record: parse_result.1,
                                    resolved_absolute_path: path.to_path_buf(),
                                    loaded_modules: FxHashMap::default(),
                                    exported_bindings_from_star_export: OnceLock::default(),
                                    export_default,
                                })),
                            ))
                        }
                    };

                    let dir = path.parent().expect("file must have a parent folder");

                    let node_tree = semantic.nodes();
                    let scope_tree = semantic.scoping();
                    let root_scope_id = scope_tree.root_scope_id();
                    let symbol_references = &mut thread_data.references;

                    for import in &module_record.borrow().module_record.import_entries {
                        let specifier = import.module_request.name;
                        if specifier.starts_with("node:") {
                            continue;
                        }

                        let resolution = resolver.resolve(dir, specifier.as_str());
                        let resolution = match resolution {
                            Ok(value) => value,
                            Err(oxc_resolver::ResolveError::Builtin {
                                resolved: _,
                                is_runtime_module: _,
                            }) => continue,
                            Err(err) => {
                                panic!(
                                    "Failed to resolve '{}' from '{}': {}",
                                    specifier,
                                    path.to_string_lossy(),
                                    err
                                )
                            }
                        };

                        let resolved_path = resolution.full_path();
                        let Ok(resolved_path_short) = resolved_path.strip_prefix(root_dir) else {
                            continue;
                        };
                        if resolved_path_short.starts_with("node_modules") {
                            continue;
                        }

                        let import_symbol_id = scope_tree
                            .get_binding(root_scope_id, import.local_name.name.as_str())
                            .expect("imported symbol to exist");
                        let import_symbol_name = match &import.import_name {
                            oxc::syntax::module_record::ImportImportName::Name(name) => {
                                name.name.as_str()
                            }
                            oxc::syntax::module_record::ImportImportName::NamespaceObject => "*",
                            oxc::syntax::module_record::ImportImportName::Default(_) => "default",
                        };

                        let Some(&module_from) = module_paths.get(resolved_path.as_path()) else {
                            continue;
                        };

                        let global_symbol_to = GlobalSymbolId {
                            module: module_from,
                            name: symbol_references.get_name_id(import_symbol_name),
                        };

                        let references_iter = scope_tree.get_resolved_references(import_symbol_id);
                        for reference in references_iter {
                            resolve_symbol_reference(
                                symbol_references,
                                module_id,
                                reference,
                                node_tree,
                                scope_tree,
                                root_scope_id,
                                global_symbol_to,
                            );
                        }
                    }

                    for (name, &symbol) in scope_tree.get_bindings(root_scope_id) {
                        let flags = scope_tree.symbol_flags(symbol);
                        if flags.is_import() {
                            continue;
                        }

                        let name_id = symbol_references.get_name_id(name);

                        let references_iter = scope_tree.get_resolved_references(symbol);
                        for reference in references_iter {
                            resolve_symbol_reference(
                                symbol_references,
                                module_id,
                                reference,
                                node_tree,
                                scope_tree,
                                root_scope_id,
                                GlobalSymbolId { module: module_id, name: name_id },
                            );
                        }
                    }
                }
            });
        }
    });

    let (semantic_map, mut symbol_references) = thread_data.into_iter().fold(
        (rustc_hash::FxHashMap::<ModuleId, _>::default(), SymbolReferences::default()),
        |mut acc, x| {
            acc.0.extend(x.semantic);
            acc.1.extend(&x.references);
            acc
        },
    );

    let elapsed_total = now.elapsed();
    println!(
        "Parsed {} files with {} symbols in {:>6.3}ms (read_dir: {:>6.3}ms; parse: {:>6.3}ms)",
        semantic_map.len(),
        symbol_references.references.len(),
        elapsed_total.as_secs_f64() * 1000f64,
        elapsed_discovery.as_secs_f64() * 1000f64,
        (elapsed_total - elapsed_discovery).as_secs_f64() * 1000f64
    );

    let names = {
        let mut names: oxc_index::IndexVec<NameId, _> = oxc_index::index_vec![std::mem::MaybeUninit::<&str>::uninit(); symbol_references.names.len()];

        for (k, &v) in &symbol_references.names {
            names[v].write(k);
        }

        // SAFETY: array elements have been initialized by the loop above
        #[expect(clippy::transmute_undefined_repr)]
        unsafe {
            std::mem::transmute::<
                oxc_index::IndexVec<NameId, std::mem::MaybeUninit<&str>>,
                oxc_index::IndexVec<NameId, &str>,
            >(names)
        }
    };

    // Populate loaded_modules
    for (_, module_record) in semantic_map.values() {
        let mut module_record = module_record.borrow_mut();
        let LinterModuleRecord {
            ref mut loaded_modules,
            ref resolved_absolute_path,
            ref module_record,
            ..
        } = *module_record;
        let dir = resolved_absolute_path.parent().unwrap();
        for specifier in module_record.requested_modules.keys() {
            let Ok(resolution) = resolver.resolve(dir, specifier) else {
                continue;
            };

            let resolved_path = resolution.full_path();
            let Some(module_id) = module_paths.get(resolved_path.as_path()) else {
                continue;
            };
            let loaded_module = Rc::downgrade(&semantic_map[module_id].1);
            loaded_modules.insert(*specifier, loaded_module);
        }
    }

    // Resolve star export bindings
    // for (_, module_record) in semantic_map.values() {
    //     let mut module_record = module_record.borrow_mut();
    //     let LinterModuleRecord {
    //         ref module_record,
    //         ref loaded_modules,
    //         ref mut exported_bindings_from_star_export,
    //         ..
    //     } = *module_record;

    //     for export_entry in &module_record.star_export_entries {
    //         let Some(remote_module_record) = export_entry
    //             .module_request
    //             .as_ref()
    //             .and_then(|module_request| loaded_modules.get(&module_request.name))
    //         else {
    //             continue;
    //         };
    //         let remote_module_record = remote_module_record.upgrade().unwrap();
    //         let remote_module_record = remote_module_record.borrow();

    //         let remote_bindings = remote_module_record
    //             .module_record
    //             .exported_bindings
    //             .keys()
    //             .map(|x| x.to_compact_str());

    //         let resolved_absolute_path = remote_module_record.resolved_absolute_path.clone();

    //         exported_bindings_from_star_export
    //             .get_mut()
    //             .unwrap()
    //             .entry(resolved_absolute_path)
    //             .or_default()
    //             .extend(remote_bindings);
    //     }
    // }

    // // Resolve start exported bindings from start exports
    // for (_, module_record) in semantic_map.values() {
    //     let mut module_record = module_record.borrow_mut();
    //     let LinterModuleRecord {
    //         ref mut exported_bindings_from_star_export,
    //         ref module_record,
    //         ref loaded_modules,
    //         ..
    //     } = *module_record;
    //     for export_entry in &module_record.star_export_entries {
    //         let Some(remote_module_record) = export_entry
    //             .module_request
    //             .as_ref()
    //             .and_then(|module_request| loaded_modules.get(&module_request.name))
    //         else {
    //             continue;
    //         };
    //         let remote_module_record = remote_module_record.upgrade().unwrap();
    //         let remote_module_record = remote_module_record.borrow();

    //         let remote_bindings = remote_module_record
    //             .exported_bindings_from_star_exports()
    //             .iter()
    //             .flat_map(|r| r.1.clone());

    //         exported_bindings_from_star_export
    //             .get_mut()
    //             .unwrap()
    //             .entry(remote_module_record.resolved_absolute_path.clone())
    //             .or_default()
    //             .extend(remote_bindings);
    //     }
    // }

    for (_, module_record) in semantic_map.values() {
        module_record.borrow().exported_bindings_from_star_exports();
    }

    // Resolve indirect references
    let mut symbol_substitutions =
        rustc_hash::FxHashMap::<GlobalSymbolId, Option<GlobalSymbolId>>::default();
    let names_map: rustc_hash::FxHashMap<&str, NameId> =
        names.iter_enumerated().map(|(id, &name)| (name, id)).collect();
    for (&module_id, (_, module_record)) in &semantic_map {
        let module_record = module_record.borrow();
        for (path, exports) in module_record.exported_bindings_from_star_export.get().unwrap() {
            let new_module_id = module_paths[path.as_path()];
            for export in exports {
                let name = names_map[export.as_str()];
                symbol_substitutions.insert(
                    GlobalSymbolId { module: module_id, name },
                    Some(GlobalSymbolId { module: new_module_id, name }),
                );
            }
        }

        for entry in &module_record.module_record.indirect_export_entries {
            let from_name = match &entry.export_name {
                oxc::syntax::module_record::ExportExportName::Name(name_span) => {
                    let Some(&id) = names_map.get(name_span.name.as_str()) else {
                        // println!(
                        //   "Unknown name: {} in {} from {}",
                        //   name_span.name().as_str(),
                        //   entry.module_request.as_ref().unwrap().name().as_str(),
                        //   module_record.resolved_absolute_path.strip_prefix(root_dir).unwrap().display()
                        // );
                        continue;
                    };

                    id
                }
                oxc::syntax::module_record::ExportExportName::Default(_) => names_map["default"],
                oxc::syntax::module_record::ExportExportName::Null => continue,
            };
            let new_name = match (&entry.local_name, &entry.import_name) {
                (_, oxc::syntax::module_record::ExportImportName::Name(name_span))
                | (
                    oxc::syntax::module_record::ExportLocalName::Name(name_span)
                    | oxc::syntax::module_record::ExportLocalName::Default(name_span),
                    _,
                ) => {
                    let Some(&id) = names_map.get(name_span.name.as_str()) else {
                        symbol_substitutions
                            .insert(GlobalSymbolId { module: module_id, name: from_name }, None);
                        continue;
                    };

                    id
                }
                (_, _) => from_name,
            };

            match &entry.module_request {
                Some(specifier) => {
                    let Some(remote_module) = module_record.loaded_modules.get(&specifier.name)
                    else {
                        symbol_substitutions
                            .insert(GlobalSymbolId { module: module_id, name: from_name }, None);
                        continue;
                    };
                    let remote_module = remote_module.upgrade().unwrap();
                    let remote_module = remote_module.borrow();
                    let remote_module_path = &remote_module.resolved_absolute_path;
                    let new_module_id = module_paths[remote_module_path.as_path()];
                    symbol_substitutions.insert(
                        GlobalSymbolId { module: module_id, name: from_name },
                        Some(GlobalSymbolId { module: new_module_id, name: new_name }),
                    );
                }
                None if from_name != new_name => {
                    symbol_substitutions.insert(
                        GlobalSymbolId { module: module_id, name: from_name },
                        Some(GlobalSymbolId { module: module_id, name: new_name }),
                    );
                }
                _ => {}
            }
        }

        for entry in &module_record.module_record.local_export_entries {
            let from_name = match &entry.export_name {
                oxc::syntax::module_record::ExportExportName::Name(name_span) => {
                    let Some(&id) = names_map.get(name_span.name.as_str()) else {
                        continue;
                    };

                    id
                }
                oxc::syntax::module_record::ExportExportName::Default(_) => names_map["default"],
                oxc::syntax::module_record::ExportExportName::Null => continue,
            };
            let new_name = match &entry.local_name {
                oxc::syntax::module_record::ExportLocalName::Name(name_span)
                | oxc::syntax::module_record::ExportLocalName::Default(name_span) => {
                    names_map[name_span.name.as_str()]
                }
                oxc::syntax::module_record::ExportLocalName::Null => {
                    continue;
                }
            };

            if from_name != new_name {
                symbol_substitutions.insert(
                    GlobalSymbolId { module: module_id, name: from_name },
                    Some(GlobalSymbolId { module: module_id, name: new_name }),
                );
            }
        }
    }

    {
        let symbol_substitutions = std::cell::UnsafeCell::new(&mut symbol_substitutions);
        #[expect(unsafe_code)]
        // SAFETY: safe
        let (symbol_substitutions_mut, symbol_substitutions_ref) = unsafe {
            (
                symbol_substitutions.get().as_mut().unwrap(),
                symbol_substitutions.get().as_ref().unwrap(),
            )
        };
        for to in symbol_substitutions_mut.values_mut() {
            let Some(to_symbol) = to else {
                continue;
            };

            let Some(&new_to) = symbol_substitutions_ref.get(to_symbol) else {
                continue;
            };
            *to = new_to;
        }
    }

    // for (&from, to) in &symbol_substitutions {
    //   let from_module = modules[from.module].strip_prefix(root_dir).unwrap();
    //   let from_name = names[from.name];

    //   match to {
    //     Some(to) => {
    //       let to_module = modules[to.module].strip_prefix(root_dir).unwrap();
    //       let to_name = names[to.name];
    //       println!("{}:{} --> {}:{}", from_module.display(), from_name, to_module.display(), to_name);
    //     }
    //     None => {
    //       println!("{}:{} --> DELETE", from_module.display(), from_name);
    //     }
    //   }
    // }

    // let debug_module = module_paths[std::path::Path::new(
    //   r"foo",
    // )];
    // let debug_module2 = module_paths[std::path::Path::new(
    //   r"bar",
    // )];
    // let debug_name = names_map["assertArrayHasNoDuplicateValues"];
    // let debug_name2 = names_map["hasNoDuplicates"];
    // let debug_symbol = GlobalSymbolId { module: debug_module, name: debug_name };
    // let debug_symbol2 = GlobalSymbolId { module: debug_module, name: debug_name2 };
    // let debug_symbol3 = GlobalSymbolId { module: debug_module2, name: debug_name };

    // Apply substitutions to symbol references
    {
        let mut delete = vec![];
        for (&_from, to) in &mut symbol_references.references {
            for (i, to) in to.iter_mut().enumerate() {
                // let mut interest = true;
                // if *to == debug_symbol {
                //   println!("[1] imported from {}:{}", modules[from.module].display(), names[from.name]);
                // } else if *to == debug_symbol2 {
                //   println!("[2] imported from {}:{}", modules[from.module].display(), names[from.name]);
                // } else if *to == debug_symbol3 {
                //   println!("[3] imported from {}:{}", modules[from.module].display(), names[from.name]);
                // } else {
                //   interest = false;
                // }

                let Some(substitution) = symbol_substitutions.get(to) else {
                    // if interest {
                    //   println!("no substitution");
                    // }
                    continue;
                };

                let Some(&substitution) = substitution.as_ref() else {
                    // if interest {
                    //   println!("delete");
                    // }
                    delete.push(i);
                    continue;
                };
                // if substitution == debug_symbol
                //   || substitution == debug_symbol2
                //   || substitution == debug_symbol3
                //   || interest
                // {
                //   println!(
                //     "{}:{} --> {}:{}",
                //     modules[to.module].display(),
                //     names[to.name],
                //     modules[substitution.module].display(),
                //     names[substitution.name]
                //   );
                // }

                *to = substitution;
            }

            for &i in delete.iter().rev() {
                to.swap_remove(i);
            }
            delete.clear();
        }
    }
    let symbol_references = symbol_references;

    // for (&from, to) in &symbol_references.references {
    //   for &to in to {
    //     if to == debug_symbol {
    //       println!("[1] referenced: {}:{}", modules[from.module].display(), names[from.name]);
    //     } else if to == debug_symbol2 {
    //       println!("[2] referenced: {}:{}", modules[from.module].display(), names[from.name]);
    //     } else if to == debug_symbol3 {
    //       println!("[3] referenced: {}:{}", modules[from.module].display(), names[from.name]);
    //     }
    //   }
    // }

    // Flatten symbol references into node array
    let nodes = {
        let mut nodes: oxc_index::IndexVec<UniqueSymbolId, _> = symbol_references
            .references
            .iter()
            .flat_map(|(&k, v)| std::iter::once(k).chain(v.iter().copied()))
            .collect();
        nodes.sort_by(|&a, &b| match a.module.cmp(&b.module) {
      std::cmp::Ordering::Equal => {
        if a.name == b.name {
          return std::cmp::Ordering::Equal;
        }

        let name_a = names[a.name];
        let name_b = names[b.name];

        match name_a {
          "*" => std::cmp::Ordering::Less,
          "<global>" => match name_b {
            "*" => std::cmp::Ordering::Greater,
            "<global>" => panic!("names should not be the same"),
            _ => std::cmp::Ordering::Less,
          },
          "default" => match name_b {
            "*" | "<global>" => std::cmp::Ordering::Greater,
            "default" => panic!("names should not be the same"),
            _ => {
              let (semantic, module_record) = &semantic_map[&a.module];
              let span_a =
                module_record.borrow().export_default.expect("module to contain default export");

              let symbol_b = semantic.scoping().get_root_binding(name_b).expect("module to contain named export");
              let span_b = oxc::span::GetSpan::span(semantic.symbol_declaration(symbol_b));

              span_a.cmp(&span_b)
            }
          },
          _ => match name_b {
            "*" | "<global>" => std::cmp::Ordering::Greater,
            "default" => {
              let (semantic, module_record) = &semantic_map[&a.module];
              let span_b =
                module_record.borrow().export_default.expect("module to contain default export");

              let symbol_a =
                semantic.scoping().get_root_binding(name_a).expect("module to contain named export");
              let span_a = oxc::span::GetSpan::span(semantic.symbol_declaration(symbol_a));

              span_a.cmp(&span_b)
            }
            _ => {
              let (semantic, module_record) = &semantic_map[&a.module];
              let module_record = module_record.borrow();
              let scope_tree = semantic.scoping();
              let root_scope = scope_tree.root_scope_id();
              let span_a = if let Some(symbol_a) = scope_tree.get_binding(root_scope, name_a) {
                scope_tree.symbol_span(symbol_a)
              } else if let Some(&span_a) = module_record.module_record.exported_bindings.get(name_a) {
                span_a
              } else {
                panic!(
                  "module to contain named export:\n  module: {}\n >name_a: {}\n  name_b: {}\n  record: {:#?}",
                  modules[a.module].strip_prefix(root_dir).unwrap().display(),
                  name_a,
                  name_b,
                  module_record
                );
              };
              let span_b = if let Some(symbol_b) = scope_tree.get_binding(root_scope, name_b) {
                scope_tree.symbol_span(symbol_b)
              } else if let Some(&span_b) = module_record.module_record.exported_bindings.get(name_b) {
                span_b
              } else {
                panic!(
                  "module to contain named export:\n  module: {}\n  name_a: {}\n >name_b: {}\n  record: {:#?}",
                  modules[a.module].strip_prefix(root_dir).unwrap().display(),
                  name_a,
                  name_b,
                  module_record
                );
              };

              span_a.cmp(&span_b)
            }
          },
        }
      }
      ord => ord,
    });

        let mut last_node = nodes[UniqueSymbolId::from_raw(0)];
        std::iter::once(last_node)
            .chain(nodes.into_iter().filter(|x| {
                let include = *x != last_node;
                last_node = *x;
                include
            }))
            .collect()
    };

    print_nodes(&nodes, &modules, root_dir, &names, out_dir);

    let depends_on: oxc_index::IndexVec<UniqueSymbolId, Vec<UniqueSymbolId>> = {
        let node_map: rustc_hash::FxHashMap<_, UniqueSymbolId> =
            nodes.iter_enumerated().map(|(idx, &value)| (value, idx)).collect();
        nodes
            .iter()
            .map(|node| {
                let Some(references) = symbol_references.references.get(node) else {
                    return vec![];
                };

                let mut references: Vec<_> = references.iter().map(|x| node_map[x]).collect();
                references.sort();

                let mut iter = references.into_iter();
                let Some(mut last_item) = iter.next() else {
                    return vec![];
                };

                std::iter::once(last_item)
                    .chain(iter.filter(|&x| {
                        let include = last_item != x;
                        last_item = x;

                        include
                    }))
                    .collect()
            })
            .collect()
    };

    print_links(&depends_on, out_dir);

    Ok(())
}

fn print_nodes(
    nodes: &oxc_index::IndexVec<UniqueSymbolId, GlobalSymbolId>,
    modules: &oxc_index::IndexVec<ModuleId, PathBuf>,
    root_dir: &str,
    names: &oxc_index::IndexVec<NameId, &str>,
    out_dir: &Path,
) {
    let file = std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(std::path::Path::join(out_dir, "nodes.ts"))
        .unwrap();
    let mut writer = std::io::BufWriter::new(file);

    writer.write_all(b"export const nodes = [\n").unwrap();
    for &GlobalSymbolId { module, name } in nodes {
        let module = modules[module].strip_prefix(root_dir).expect("module to be under root dir");
        let name = names[name];
        writer
            .write_fmt(format_args!(
                "  \"{}:{}\",\n",
                module.to_string_lossy().replace('\\', "/"),
                name
            ))
            .unwrap();
    }

    writer.write_all(b"];").unwrap();
    writer.flush().unwrap();
}

fn print_links(links: &oxc_index::IndexVec<UniqueSymbolId, Vec<UniqueSymbolId>>, out_dir: &Path) {
    let file = std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(std::path::Path::join(out_dir, "links.ts"))
        .unwrap();
    let mut writer = std::io::BufWriter::new(file);

    writer.write_all(b"export const links = [\n").unwrap();
    for links in links {
        writer.write_all(b"  [").unwrap();
        let mut links = links.iter();
        if let Some(&link) = links.next() {
            writer.write_fmt(format_args!("{}", link.raw())).unwrap();
        }

        for &link in links {
            writer.write_fmt(format_args!(", {}", link.raw())).unwrap();
        }
        writer.write_all(b"],\n").unwrap();
    }

    writer.write_all(b"];").unwrap();
    writer.flush().unwrap();
}

fn resolve_symbol_reference(
    symbol_references: &mut SymbolReferences,
    module_id: ModuleId,
    reference: &oxc::semantic::Reference,
    node_tree: &oxc::semantic::AstNodes<'_>,
    scope_tree: &oxc::semantic::Scoping,
    root_scope_id: oxc::semantic::ScopeId,
    global_symbol_to: GlobalSymbolId,
) {
    let node_id = reference.node_id();
    let Some(parent) = node_tree
        .ancestors(node_id)
        .find(|x| x.scope_id() == root_scope_id && x.kind().is_declaration())
    else {
        let name = symbol_references.get_name_id("<global>");
        symbol_references
            .add_symbol_reference(GlobalSymbolId { module: module_id, name }, global_symbol_to);
        return;
    };

    match parent.kind() {
        oxc::ast::AstKind::TSTypeAliasDeclaration(decl) => {
            let name =
                scope_tree.symbol_name(decl.id.symbol_id.get().expect("Symbol to be resolved"));
            let name = symbol_references.get_name_id(name);
            symbol_references
                .add_symbol_reference(GlobalSymbolId { module: module_id, name }, global_symbol_to);
        }
        oxc::ast::AstKind::Function(decl) => match decl.id.as_ref() {
            Some(id) => match decl.r#type {
                oxc::ast::ast::FunctionType::FunctionDeclaration => {
                    let name =
                        scope_tree.symbol_name(id.symbol_id.get().expect("Symbol to be resolved"));
                    let name = symbol_references.get_name_id(name);
                    symbol_references.add_symbol_reference(
                        GlobalSymbolId { module: module_id, name },
                        global_symbol_to,
                    );
                }
                oxc::ast::ast::FunctionType::TSDeclareFunction => {
                    let symbol = scope_tree.get_binding(root_scope_id, &id.name);
                    let name = scope_tree.symbol_name(symbol.expect("Symbol to be resolved"));
                    let name = symbol_references.get_name_id(name);
                    symbol_references.add_symbol_reference(
                        GlobalSymbolId { module: module_id, name },
                        global_symbol_to,
                    );
                }
                _ => panic!("Unknown function declaration type: {}", decl.r#type as u8),
            },
            None => match node_tree.parent_kind(parent.id()) {
                oxc::ast::AstKind::ExportDefaultDeclaration(_) => {
                    let name = symbol_references.get_name_id("default");
                    symbol_references.add_symbol_reference(
                        GlobalSymbolId { module: module_id, name },
                        global_symbol_to,
                    );
                }
                _ => panic!("Unknown anonymous function declaration"),
            },
        },
        oxc::ast::AstKind::Class(decl) => {
            let name = scope_tree.symbol_name(
                decl.id
                    .as_ref()
                    .expect("class to be named")
                    .symbol_id
                    .get()
                    .expect("Symbol to be resolved"),
            );
            let name = symbol_references.get_name_id(name);
            symbol_references
                .add_symbol_reference(GlobalSymbolId { module: module_id, name }, global_symbol_to);
        }
        oxc::ast::AstKind::TSInterfaceDeclaration(decl) => {
            let name =
                scope_tree.symbol_name(decl.id.symbol_id.get().expect("Symbol to be resolved"));
            let name = symbol_references.get_name_id(name);
            symbol_references
                .add_symbol_reference(GlobalSymbolId { module: module_id, name }, global_symbol_to);
        }
        oxc::ast::AstKind::VariableDeclaration(decl_list) => {
            for decl in &decl_list.declarations {
                match &decl.id.kind {
                    oxc::ast::ast::BindingPatternKind::BindingIdentifier(id) => {
                        let name = scope_tree
                            .symbol_name(id.symbol_id.get().expect("Symbol to be resolved"));
                        let name = symbol_references.get_name_id(name);
                        symbol_references.add_symbol_reference(
                            GlobalSymbolId { module: module_id, name },
                            global_symbol_to,
                        );
                    }
                    oxc::ast::ast::BindingPatternKind::ObjectPattern(pat) => {
                        for prop in &pat.properties {
                            match &prop.value.kind {
                                oxc::ast::ast::BindingPatternKind::BindingIdentifier(id) => {
                                    let name = scope_tree.symbol_name(
                                        id.symbol_id.get().expect("Symbol to be resolved"),
                                    );
                                    let name = symbol_references.get_name_id(name);
                                    symbol_references.add_symbol_reference(
                                        GlobalSymbolId { module: module_id, name },
                                        global_symbol_to,
                                    );
                                }
                                _ => panic!("Unknown nested binding pattern"),
                            }
                        }
                    }
                    _ => panic!("Unknown binding pattern"),
                }
            }
        }
        oxc::ast::AstKind::ExportDefaultDeclaration(_) => {
            let name = symbol_references.get_name_id("default");
            symbol_references
                .add_symbol_reference(GlobalSymbolId { module: module_id, name }, global_symbol_to);
        }
        oxc::ast::AstKind::ExportNamedDeclaration(_) => {
            // import {foo} from 'foo';
            // export {foo}
            let oxc::ast::AstKind::ExportSpecifier(node) =
                node_tree.parent_kind(reference.node_id())
            else {
                panic!("Expected identifier reference parent node to be export specifier");
            };
            let name = node.exported.name();
            let name = symbol_references.get_name_id(name.as_str());
            symbol_references
                .add_symbol_reference(GlobalSymbolId { module: module_id, name }, global_symbol_to);
        }
        oxc::ast::AstKind::ImportDeclaration(_)
        | oxc::ast::AstKind::ExportAllDeclaration(_)
        | oxc::ast::AstKind::TSExportAssignment(_)
        | oxc::ast::AstKind::TSNamespaceExportDeclaration(_)
        | oxc::ast::AstKind::TSModuleDeclaration(_) => {}
        // oxc::ast::AstKind::ModuleDeclaration(_decl) => {
        //     // let name = decl.id.name();
        //     // let name = symbol_references.get_name_id(name.as_str());
        //     // symbol_references
        //     //   .add_symbol_reference(GlobalSymbolId { module: module_id, name }, global_symbol_to);
        // }
        x => {
            panic!("Unknown declaration type: {}", x.debug_name());
        }
    }
}
