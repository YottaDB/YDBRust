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
use yottadb::{YDB_NOTTP, DeleteType};

fn main() {
    let err_buffer = Vec::with_capacity(1024);
    let hello = Key::new("hello", &["Rust"]);
    let err_buffer = hello.set_st(YDB_NOTTP, err_buffer, "こんにちは".as_bytes()).unwrap();

    let out_buffer = Vec::with_capacity(100);
    let out_buffer = hello.get_st(YDB_NOTTP, out_buffer).unwrap();
    assert_eq!(out_buffer, "こんにちは".as_bytes());
    hello.delete_st(YDB_NOTTP, err_buffer, DeleteType::DelNode).unwrap();
}
