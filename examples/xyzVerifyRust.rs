#![allow(non_snake_case)]

use std::process;

use yottadb::context_api::Context;
use yottadb::simple_api::{Key, YDBError};
use yottadb::craw::YDB_ERR_NODEEND;

fn main() {
    let ctx = Context::new();
    let mut crab = ctx.new_key(Key::new("^Crab", &["0"]));
    let mut delta = ctx.new_key(Key::new("^Delta", &["0"]));
    let mut horse = ctx.new_key(Key::new("^Horse", &["0"]));

    assert_eq!(crab.get(), Ok("0".into()));
    assert_eq!(horse.get(), Ok("0".into()));

    let mut delta_sum: i64 = 0;
    loop {
        match (crab.next_sub_self(), delta.next_sub_self(), horse.next_sub_self()) {
            (Err(YDBError { status: YDB_ERR_NODEEND, .. }),
             Err(YDBError { status: YDB_ERR_NODEEND, .. }),
             Err(YDBError { status: YDB_ERR_NODEEND, .. })) => break,
            (Ok(_), Ok(_), Ok(_)) => {}
            other => {
                println!("error retrieving values: {:?}", other);
                process::exit(1);
             }
        };

        let toString = String::from_utf8_lossy;
        let (crab_t, delta_t, horse_t) = (toString(&crab[1]), toString(&delta[1]), toString(&horse[1]));

        // confirm that timestamps match
        if crab[1] != delta[1] || delta[1] != horse[1] {
            println!("ACID fail: tDelta={}; tCrab={}; tHorse={}", delta_t, crab_t, horse_t);
            process::exit(1);
        }
        let t = crab_t.into_owned();

        let (crab_val, delta_val, horse_val): (i64, i64, i64) = (
            toString(&crab.get().unwrap()).parse().unwrap(),
            toString(&delta.get().unwrap()).parse().unwrap(),
            toString(&horse.get().unwrap()).parse().unwrap(),
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
}
