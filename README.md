# TypeScript Symbolic dependency graph

A small utility to build symbol dependency graph for a TypeScript project. It probably does not work and is very hacked together. Or maybe it does, I don't know - it printed something to the output files for a large project I tested this on.

The idea was to collect which top-level declarations are referencing which symbols and build a graph of such references by resolving symbols globally. It also should handle indirect symbol references (i.e. resolving symbols from barrel files).

## How to run this?

```sh
cargo run --bin splitter /path/to/TypeScript/repo /path/to/out/dir
```

### Example

Given the following source files:

```ts
import {foo} from '@/foo.ts';

let x = foo();

export function bar() {
  ...
  for (...) {
    if (...) {
       foo();

       x += 5;
    }
  }

  ...
}
```

It should produce a graph like this (as `nodes.ts` and `links.ts`):

```
bar.ts:x --> foo.ts:foo
bar.ts:bar --> bar.ts:x
bar.ts:bar --> foo.ts:foo
```
