#!/bin/sh
cargo fmt -- --check
cargo clippy -- --deny clippy::all
cargo test
