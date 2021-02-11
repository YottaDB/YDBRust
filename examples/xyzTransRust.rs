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
//! Update a multi-region database using ACID transactions
//! This program is part of the exercises in the YottaDB Acculturation Workshop at
//! https://docs.yottadb.com/AcculturationGuide/acculturation.html
//! and its use is discussed there.
//!
//! This is a simulated application program which uses the database from multiple threads.
#![allow(non_snake_case)]

use std::error::Error;
use std::time::{Duration, SystemTime};

use rand::Rng;
use yottadb::{Context, KeyContext, TransactionStatus};

fn main() -> Result<(), Box<dyn Error + Send + Sync>> {
    let mut rng = rand::thread_rng();
    let ctx = Context::new();

    loop {
        ctx.tp(
            |ctx| {
                let us = SystemTime::now()
                    .duration_since(SystemTime::UNIX_EPOCH)?
                    .as_micros()
                    .to_string();
                let n: i64 = rng.gen::<i32>().into();

                // ^Delta(us) = n
                let delta = KeyContext::new(&ctx, "^Delta", &[us.as_bytes()]);
                delta.set(n.to_string())?;

                // ^Crab(ms) = ^Crab(lasttime) - n
                let crab = KeyContext::new(&ctx, "^Crab", &[us.as_bytes()]);
                let mut last_crab = crab.clone();
                last_crab.prev_sub_self()?;
                let last_crab_val: i64 = std::str::from_utf8(&last_crab.get()?)?.parse()?;
                crab.set((last_crab_val - n).to_string())?;

                // ^Horse(ms) = ^Horse(lasttime) + n
                let horse = KeyContext::new(&ctx, "^Horse", &[us]);
                let mut last_horse = horse.clone();
                last_horse.prev_sub_self()?;
                let last_horse_val: i64 = String::from_utf8_lossy(&last_horse.get()?).parse()?;
                horse.set((last_horse_val + n).to_string())?;

                Ok(TransactionStatus::Ok)
            },
            "BATCH",
            &[],
        )?;
        std::thread::sleep(Duration::from_millis(500));
    }
}
