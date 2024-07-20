#!/usr/bin/env -S just --justfile

set windows-shell := ["pwsh", "-c"]
set shell := ["bash", "-cu"]

_default:
  @just --list -u

# Make sure you have cargo-binstall installed.
# You can download the pre-compiled binary from <https://github.com/cargo-bins/cargo-binstall#installation>
# or install via `cargo install cargo-binstall`
# Initialize the project by installing all the necessary tools.
init:
  cargo binstall cargo-shear dprint -y

# Format all files
fmt:
  -cargo shear --fix
  cargo fmt --all
  dprint fmt

fix:
  cargo clippy --fix --allow-staged --no-deps
  just fmt
