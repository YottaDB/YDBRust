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

use yottadb::{simple_api, YDB_NOTTP, ydb_exit};

#[test]
fn test_exit_before_init() {
    // If called before any previous ydb_* call, should do nothing.
    ydb_exit();
    simple_api::Key::variable("a").data_st(YDB_NOTTP, Vec::new()).unwrap();
}
