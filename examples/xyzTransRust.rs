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
//! This is a simulated application program which uses the database from multiple threads.
#![allow(non_snake_case)]

use std::error::Error;
use std::time::{Duration, SystemTime};
use std::sync::atomic::{AtomicBool, Ordering};

use rand::Rng;
use yottadb::TransactionStatus;
use yottadb::context_api::{Context, KeyContext};

static KILL_SWITCHES: [AtomicBool; 5] = [
    AtomicBool::new(false),
    AtomicBool::new(false),
    AtomicBool::new(false),
    AtomicBool::new(false),
    AtomicBool::new(false),
];

fn main() -> Result<(), Box<dyn Error + Send + Sync>> {
    use std::thread;

    let handles: Vec<_> = (0..5).map(|i| thread::spawn(move || trans(i))).collect();
    println!("finished spawn");
    thread::sleep(Duration::from_secs(5));
    println!("finished sleep");

    for switch in &KILL_SWITCHES {
        // see comment by load below for explanation of ordering
        switch.store(true, Ordering::SeqCst);
    }
    println!("finished kill");

    for handle in handles {
        handle.join().expect("no thread should panic")?;
    }
    println!("all threads joined");

    Ok(())
}

fn trans(i: usize) -> Result<(), Box<dyn Error + Send + Sync>> {
    println!("spawned {}", i);

    let mut rng = rand::thread_rng();
    let ctx = Context::new();

    loop {
        // this could probably use Relaxed but I don't care about the performance
        // and I don't want someone to copy it (since Relaxed only works if this
        // is the _only_ communication between threads).
        if KILL_SWITCHES[i].load(Ordering::SeqCst) {
            return Ok(());
        }
        ctx.tp(
            |ctx| {
                let us = SystemTime::now()
                    .duration_since(SystemTime::UNIX_EPOCH)?
                    .as_micros()
                    .to_string();
                let n: i64 = rng.gen::<i32>().into();

                // ^Delta(ms) = n
                let delta = KeyContext::new(&ctx, "^Delta", &[us.as_bytes()]);
                delta.set(n.to_string())?;

                // ^Crab(ms) = ^Crab(lasttime) - n
                let crab = KeyContext::new(&ctx, "^Crab", &[us.as_bytes()]);
                let last_crab = crab.prev_sub()?;
                let last_crab_val: i64 = String::from_utf8_lossy(&last_crab.get()?).parse()?;
                crab.set((last_crab_val - n).to_string())?;

                // ^Horse(ms) = ^Horse(lasttime) + n
                let horse = KeyContext::new(&ctx, "^Horse", &[us]);
                let last_horse = horse.prev_sub()?;
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
