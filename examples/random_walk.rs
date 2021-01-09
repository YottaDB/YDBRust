/****************************************************************
*                                                               *
* Copyright (c) 2019-2021 YottaDB LLC and/or its subsidiaries.  *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

#[macro_use]
extern crate yottadb;
extern crate threadpool;
extern crate rand;

use std::{thread, time};

use threadpool::ThreadPool;

use yottadb::context_api::Context;
use yottadb::DeleteType;

use rand::Rng;

fn get_global() -> &'static str {
    match rand::thread_rng().gen_range(0..=2) {
        0 => "^MyGlobal1",
        1 => "^MyGlobal2",
        2 => "^MyGlobal3",
        _ => unreachable!(),
    }
}

fn random_walk(ctx: &Context) {
    let mut key =
        make_ckey!(ctx, get_global(), get_global(), get_global(), get_global(), get_global());
    // Randomly select between 0 and 4 subscripts
    let mut rng = rand::thread_rng();
    key.truncate(rng.gen_range(0..=4));
    // Select a random operation
    match rng.gen_range(0..=6) {
        0 => key.delete(DeleteType::DelNode).unwrap(),
        1 | 4 | 5 => match key.get() {
            // we don't unwrap this because failures are fine
            _ => (),
        },
        2 => key.set(b"Hello world!").unwrap(),
        3 => {
            key.increment(None).unwrap();
        }
        6 => {
            key.data().unwrap();
        }
        _ => unreachable!(),
    }
}

fn main() {
    let pool = ThreadPool::new(8);
    for _ in 0..8 {
        pool.execute(move || {
            let ctx = Context::new();
            loop {
                random_walk(&ctx);
            }
        });
    }

    thread::sleep(time::Duration::from_secs(10));
}
