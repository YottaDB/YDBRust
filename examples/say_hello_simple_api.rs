/****************************************************************
*                                                               *
* Copyright (c) 2020 YottaDB LLC and/or its subsidiaries.  *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

//! An example of `yottadb` using the `simple_api`.

use yottadb::simple_api::Key;
use yottadb::YDB_NOTTP;

fn main() {
    let hello = Key::new("^hello", &["Rust"]);
    hello.set_st(YDB_NOTTP, Vec::new(), "こんにちは".as_bytes()).unwrap();

    let out_buffer = hello.get_st(YDB_NOTTP, Vec::new()).unwrap();
    assert_eq!(out_buffer, "こんにちは".as_bytes());
}