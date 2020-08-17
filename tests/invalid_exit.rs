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
#[test]
fn test_invalid_exit() {
    use std::ffi::CString;
    use std::env::set_var;
    use std::os::raw::c_ulong;
    use yottadb::{
        ci_t,
        craw::{self, ydb_string_t},
        YDB_NOTTP,
    };

    set_var("ydb_routines", "examples/m-ffi");
    set_var("ydb_ci", "examples/m-ffi/calltab.ci");
    set_var("ydb_xc_c", "examples/m-ffi/external.xc");

    // `INVYDBEXIT` should be returned if `exit` is called through M FFI
    let mut buf = Vec::<u8>::with_capacity(150);

    let mut status =
        ydb_string_t { address: buf.as_mut_ptr() as *mut _, length: buf.capacity() as c_ulong };
    let exit = CString::new("ydb_exit").unwrap();
    unsafe {
        ci_t!(YDB_NOTTP, Vec::new(), &exit, &mut status as *mut ydb_string_t).unwrap();
        buf.set_len(status.length as usize);
    }

    let msg = String::from_utf8_lossy(&buf);
    println!("{:?}", msg);
    let status = msg.split(',').next().unwrap().parse().expect("status should be valid number");
    assert_eq!(-craw::YDB_ERR_INVYDBEXIT, status);
}
