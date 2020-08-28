/****************************************************************
*                                                               *
* Copyright (c) 2019-2020 YottaDB LLC and/or its subsidiaries.  *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

//! Regression test for https://gitlab.com/YottaDB/Lang/YDBRust/-/issues/34
use std::convert::TryInto;
use std::env::set_var;
use std::ffi::CString;
use std::os::raw::c_ulong;

use yottadb::{
    YDB_NOTTP,
    craw::{self, YDB_ERR_INVSTRLEN, YDB_MAX_STR, ydb_string_t},
    simple_api::{DEFAULT_CAPACITY, Key},
    ci_t,
};

#[test]
fn ydb_ci_t() {
    set_var("ydb_routines", "examples/m-ffi");
    set_var("ydb_ci", "examples/m-ffi/calltab.ci");

    let mut out_buffer = Vec::new();
    let mut status = ydb_string_t {
        address: out_buffer.as_mut_ptr() as *mut _,
        length: out_buffer.capacity() as c_ulong,
    };
    let routine = CString::new("HelloWorld1").unwrap();
    // Allocate a buffer with the maximum capacity so we're sure that any INVSTRLEN is for `out_buffer`, not `err_buffer`.
    let capacity = YDB_MAX_STR.try_into().expect("16-bit platforms are not supported");
    let err_buffer = Vec::with_capacity(capacity);
    let err = unsafe {
        ci_t!(YDB_NOTTP, err_buffer, &routine, &mut status as *mut ydb_string_t).unwrap_err()
    };
    assert_eq!(err.status, YDB_ERR_INVSTRLEN);
}

#[test]
fn ydb_node_st() {
    use yottadb::context_api::{Context, KeyContext};

    // `set ^x(1)=aaaaa,^x(2)=bbbbb`
    let ctx = Context::new();
    let mut key = KeyContext::new(&ctx, "x", &["1"]);
    key.set("a".repeat(DEFAULT_CAPACITY + 1)).unwrap();
    key[0] = "2".into();
    key.set("b".repeat(DEFAULT_CAPACITY + 1)).unwrap();
    // Make sure we don't use this by accident later
    drop(key);

    // Go to the end of the nodes
    let mut iter_key = Key::variable("x");
    iter_key.node_next_self_st(YDB_NOTTP, Vec::with_capacity(5)).unwrap();
    assert_eq!(
        iter_key[0],
        b"1",
        "{0}({1}) != {0}(1)",
        iter_key.variable,
        String::from_utf8_lossy(&iter_key[0])
    );
    iter_key.node_next_self_st(YDB_NOTTP, Vec::with_capacity(5)).unwrap();
    assert_eq!(iter_key[0], b"2");

    // Check for YDB_ERR_NODEEND
    // NOTE: this has knowledge of how the `simple_api` works internally.
    // If the vec has _any_ non-zero capacity, it will not be resized.
    let err = iter_key.node_next_self_st(YDB_NOTTP, Vec::with_capacity(1)).unwrap_err();
    assert_eq!(err.status, craw::YDB_ERR_NODEEND);
    eprintln!("{}", String::from_utf8(err.message).unwrap());

    // Check for YDB_ERR_INVVARNAME
    iter_key.variable = "a_b_c".to_string();
    let err = iter_key.node_next_self_st(YDB_NOTTP, Vec::with_capacity(1)).unwrap_err();
    assert_eq!(err.status, craw::YDB_ERR_INVVARNAME);
    eprintln!("{}", String::from_utf8(err.message).unwrap());
}
