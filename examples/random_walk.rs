#[macro_use]
extern crate yottadb;
extern crate threadpool;
extern crate rand;

use std::{thread, time};

use threadpool::ThreadPool;

use yottadb::context_api::Context;
use yottadb::simple_api::DeleteType;

use rand::Rng;

fn get_global() -> String {
    let mut rng = rand::thread_rng();
    let val = rng.gen_range(0, 2);
    match val {
        0 => String::from("^MyGlobal1"),
        1 => String::from("^MyGlobal2"),
        2 => String::from("^MyGlobal3"),
        _ => panic!("Huh.")
    }
}

fn random_walk() {
    let ctx = Context::new();
    let mut key = make_ckey!(ctx, get_global(), get_global(), get_global(), get_global(), get_global());
    // Randomly select between 0 and 4 subscripts
    let mut rng = rand::thread_rng();
    key.truncate(rng.gen_range(1, 5));
    // Select a random operation
    match rng.gen_range(0, 6) {
        0 => key.delete(DeleteType::DelNode).unwrap(),
        1 => match key.get() { _ => (), }, // we don't unwrap this because failures are fine
        2 => key.set(b"Hello world!").unwrap(),
        3 => {
            key.increment(None).unwrap();
        },
        4 => match key.next_sub_self() { _ => (), },
        5 => match key.prev_sub_self() { _ => (), },
        6 => {
            key.data().unwrap();
        },
        _ => panic!("out of range"),
    }
}

fn main() {
    let pool = ThreadPool::new(8);
    for _ in 0..8 {
        pool.execute(move || {
            loop {
                random_walk();
            }
        });
    }

    thread::sleep(time::Duration::from_secs(30));
}
