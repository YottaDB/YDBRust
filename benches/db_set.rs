/****************************************************************
*                                                               *
* Copyright (c) 2020 YottaDB LLC and/or its subsidiaries.       *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

//! This implements the following M line,
//! except that the number of iterations is not fixed.
//!
//! ```mumps
//! for i=0:1:999999 set ^hello(i)=$j
//! ```

use std::process;
use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use yottadb::context_api::{Context, KeyContext};

fn criterion_boilerplate(c: &mut Criterion, name: &str, mut do_the_work: impl FnMut(i32)) {
    let mut i = 0;
    c.bench_function(name, |b| {
        let get_id = || {
            i += 1;
            i
        };
        b.iter_batched(get_id, &mut do_the_work, BatchSize::SmallInput);
    });
}

/// An inefficient example of `yottadb` using the `context_api`.
///
/// For a comparison to a more efficient example, see `set_no_allocate()`.
pub fn set_allocate(c: &mut Criterion) {
    // Calculates the process ID, but does not convert it to a string
    let pid = process::id();
    // This creates a buffer, but performs no allocation.
    let ctx = Context::new();

    // Repeatedly perform a `set`.
    criterion_boilerplate(c, "set allocating", |i| {
        // This allocates three times:
        // 1. Once to copy "^hello"
        // 2. Once to format `i` into a string
        // 3. Once when the `&str` from `as_str()` is copied into the subscript
        let hello = KeyContext::new(&ctx, "^hello", &[i.to_string().as_str()]);
        // This allocates a buffer for the `pid` in each iteration of the loop.
        hello.set(pid.to_string()).unwrap();
    })
}

/// An efficient example of `yottadb` using the `context_api`.
///
/// To see why this is efficient, compare this to `set_allocate()`.
pub fn set_no_allocate(c: &mut Criterion) {
    // Calculate the process ID once to avoid allocating in a loop.
    let pid = process::id().to_string().into_bytes();

    // This creates a buffer, but performs no allocation.
    let ctx = Context::new();
    // This is the first time the `ctx` will allocate.
    let mut hello = KeyContext::new(&ctx, "^hello", &["0"]);

    // Repeatedly perform a `set`.
    criterion_boilerplate(c, "set without allocating", |i| {
        // Change the subscript to `hello(i)`.
        // Note that this reuses the existing `hello` variable,
        // to avoid reallocating the variable name.
        hello[0] = i.to_string().into_bytes();
        // Set the subscript to `pid`. This makes a copy of the bytes.
        // It will allocate if `ydb_set_st` returns an error, but not otherwise.
        hello.set(&pid).unwrap();
    });
}

criterion_group!(benches, set_allocate, set_no_allocate);
criterion_main!(benches);
