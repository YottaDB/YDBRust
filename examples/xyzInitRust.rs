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
#![allow(non_snake_case)]

//! Update a multi-region database using ACID transactions
//! This program is part of the exercises in the YottaDB Acculturation Workshop at
//! https://docs.yottadb.com/AcculturationGuide/acculturation.html
//! and its use is discussed there.
use yottadb::{DeleteType, YDBResult};
use yottadb::context_api::{Context, KeyContext as Key};

fn main() -> YDBResult<()> {
    // Set up the keys
    let ctx = Context::new();
    let mut crab = Key::variable(&ctx, "^Crab");
    let delta = Key::variable(&ctx, "^Delta");
    let mut horse = Key::variable(&ctx, "^Horse");

    // Remove existing trees
    crab.delete(DeleteType::DelTree)?;
    delta.delete(DeleteType::DelTree)?;
    horse.delete(DeleteType::DelTree)?;

    // Set initial values
    let zero = b"0".to_vec();
    crab.push(zero.clone());
    crab.set("0")?;
    horse.push(zero);
    horse.set("0")?;

    Ok(())
}
