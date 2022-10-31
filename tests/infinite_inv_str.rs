/****************************************************************
*                                                               *
* Copyright (c) 2019-2022 YottaDB LLC and/or its subsidiaries.  *
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
use std::os::raw::c_char;

use yottadb::{
    YDB_NOTTP,
    craw::{YDB_MAX_STR, ydb_string_t},
    ci_t,
};

#[test]
fn ydb_ci_t() {
    set_var("ydb_routines", "examples/m-ffi");
    set_var("ydb_ci", "examples/m-ffi/calltab.ci");

    let mut out_buffer = Vec::<u8>::new();
    let mut status = ydb_string_t {
        address: out_buffer.as_mut_ptr() as *mut c_char,
        length: out_buffer.capacity() as c_ulong,
    };
    let routine = CString::new("HelloWorld1").unwrap();
    // Allocate a buffer with the maximum capacity so we're sure that any INVSTRLEN is for `out_buffer`, not `err_buffer`.
    let capacity = YDB_MAX_STR.try_into().expect("16-bit platforms are not supported");
    let err_buffer = Vec::with_capacity(capacity);
    unsafe { ci_t!(YDB_NOTTP, err_buffer, &routine, &mut status as *mut ydb_string_t).unwrap() };
    // After YDB#564, an INVSTRLEN is no longer returned for `out_buffer`. Instead a truncated buffer is returned.
    // In this case, since `out_buffer` was allocated with 0 bytes to start with, we expect a 0-byte return value.
    // Hence the assert below against an empty string.
    assert_eq!(out_buffer, b"");
}
