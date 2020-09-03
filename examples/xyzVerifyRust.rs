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
//! Update a multi-region database using ACID transactions
//! This program is part of the exercises in the YottaDB Acculturation Workshop at
//! https://docs.yottadb.com/AcculturationGuide/acculturation.html
//! and its use is discussed there.
//!
//! This program verifies that the database ensures ACID properties.
#![allow(non_snake_case)]

use std::error::Error;
use std::process;
use yottadb::YDBError;
use yottadb::context_api::{Context, KeyContext as Key};
use yottadb::craw::YDB_ERR_NODEEND;

fn main() -> Result<(), Box<dyn Error>> {
    let ctx = Context::new();
    let mut crab = Key::new(&ctx, "^Crab", &["0"]);
    let mut delta = Key::new(&ctx, "^Delta", &["0"]);
    let mut horse = Key::new(&ctx, "^Horse", &["0"]);

    assert_eq!(crab.get(), Ok("0".into()));
    assert_eq!(horse.get(), Ok("0".into()));

    let mut delta_sum: i64 = 0;
    loop {
        match (crab.next_sub_self(), delta.next_sub_self(), horse.next_sub_self()) {
            (
                Err(YDBError { status: YDB_ERR_NODEEND, .. }),
                Err(YDBError { status: YDB_ERR_NODEEND, .. }),
                Err(YDBError { status: YDB_ERR_NODEEND, .. }),
            ) => break,
            (Ok(_), Ok(_), Ok(_)) => {}
            other => {
                println!("error retrieving values: {:?}", other);
                process::exit(1);
            }
        };

        let to_string = String::from_utf8_lossy;
        let (crab_t, delta_t, horse_t) =
            (to_string(&crab[0]), to_string(&delta[0]), to_string(&horse[0]));

        // confirm that timestamps match
        if crab[0] != delta[0] || delta[0] != horse[0] {
            println!("ACID fail: tDelta={}; tCrab={}; tHorse={}", delta_t, crab_t, horse_t);
            process::exit(1);
        }
        let t = crab_t.into_owned();

        let (crab_val, delta_val, horse_val): (i64, i64, i64) = (
            to_string(&crab.get()?).parse()?,
            to_string(&delta.get()?).parse()?,
            to_string(&horse.get()?).parse()?,
        );
        // confirm crab + horse == 0
        if crab_val.wrapping_add(horse_val) != 0 {
            println!("ACID fail: ^Crab({})={}; ^Horse({})={}", t, crab_val, t, horse_val);
            process::exit(2);
        }
        // confirm horse == sum(delta) for all delta up to now
        delta_sum = delta_sum.wrapping_add(delta_val);
        if horse_val != delta_sum {
            println!("ACID fail: Sum ^Delta(0:{})={}; ^Horse({})={}", t, delta_sum, t, horse_val);
            process::exit(3);
        }
    }

    println!("ACID test pass");
    Ok(())
}
