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

//! This example program demonstrates what might happen if you don't
//! call `eintr_handler` in a long-running transaction.
//! See [Signal Handling] for more details about `eintr_handler`.
//!
//! [Signal Handling]: https://yottadb.gitlab.io/Lang/YDBRust/yottadb/index.html#signal-handling

use yottadb::YDBResult;
use yottadb::context_api::Context;

fn main() -> YDBResult<()> {
    let ctx = Context::new();
    ctx.tp(
        |_ctx| {
            loop {
                std::thread::sleep(std::time::Duration::from_secs(1));
                println!("finished 1 second sleep");
                // uncomment this line to see the behavior when calling the handler
                //ctx.eintr_handler().unwrap();
            }
        },
        "BATCH",
        &[],
    )
    .unwrap();
    unreachable!()
}
