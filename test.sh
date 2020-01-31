#!/bin/sh
# commented out until I convert the project to use `rustfmt` formatting
#cargo fmt -- --check
cargo clippy -- --deny clippy::all
cargo test
