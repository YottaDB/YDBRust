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

//! An example of `yottadb` using the `context_api`.

use yottadb::context_api::{Context, KeyContext as Key};
use yottadb::{DeleteType, YDBError};

fn main() -> Result<(), YDBError> {
    let ctx = Context::new();
    let hello = Key::new(&ctx, "hello", &["Rust"]);
    hello.set("こんにちは")?;

    assert_eq!(hello.get()?, "こんにちは".as_bytes());
    hello.delete(DeleteType::DelNode)
}
