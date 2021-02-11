/****************************************************************
*                                                               *
* Copyright (c) 2020-2021 YottaDB LLC and/or its subsidiaries.  *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

use yottadb::{Context, KeyContext, craw, ydb_exit};

#[test]
fn test_exit() {
    // Calls should work to start
    let key = KeyContext::variable(&Context::new(), "a");
    key.data().unwrap();
    ydb_exit();
    // Then calls return CALLINAFTERXIT after calling `exit()`
    let err = key.data().unwrap_err();
    assert_eq!(err.status, craw::YDB_ERR_CALLINAFTERXIT);
}
