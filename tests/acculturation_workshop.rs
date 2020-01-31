#![allow(non_snake_case)]

//! Update a multi-region database using ACID transactions
//! This program is part of the exercises in the YottaDB Acculturation Workshop at
//! https://docs.yottadb.com/AcculturationGuide/acculturation.html
//! and its use is discussed there.
//!
//! For the sake of simplicity, this program does no error handling.
use std::time::{Duration, SystemTime};
use std::sync::atomic::{AtomicBool, Ordering};

use rand::Rng;
use yottadb::context_api::{Context, KeyContext};
use yottadb::simple_api::{DeleteType, Key, YDBError};

static KILL_SWITCHES: [AtomicBool; 5] = [
    AtomicBool::new(false),
    AtomicBool::new(false),
    AtomicBool::new(false),
    AtomicBool::new(false),
    AtomicBool::new(false),
];

#[test]
fn main() {
    use std::thread;

    init();
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
        handle.join().expect("no thread should panic");
    }
    println!("all threads joined");
    verify();
}

fn init() {
    let ctx = Context::new();
    let mut crab = ctx.new_key("^Crab");
    let mut delta = ctx.new_key("^Delta");
    let mut horse = ctx.new_key("^Horse");

    // remove existing trees
    crab.delete(DeleteType::DelTree).unwrap();
    delta.delete(DeleteType::DelTree).unwrap();
    horse.delete(DeleteType::DelTree).unwrap();

    // set initial values
    let mut crab = ctx.new_key(Key::new("^Crab", &["0"]));
    let mut horse = ctx.new_key(Key::new("^Horse", &["0"]));
    crab.set("0").unwrap();
    horse.set("0").unwrap();
}

fn trans(i: usize) {
    println!("spawned {}", i);

	let mut rng = rand::thread_rng();
	let ctx = Context::new();

	loop {
        // this could probably use Relaxed but I don't care about the performance
        // and I don't want someone to copy it (since Relaxed only works if this
        // is the _only_ communication between threads).
        if KILL_SWITCHES[i].load(Ordering::SeqCst) {
            return;
        }
		ctx.tp(|ctx| {
			let us = SystemTime::now()
				.duration_since(SystemTime::UNIX_EPOCH)
				.unwrap()
				.as_micros()
				.to_string();
			let n: i64 = rng.gen::<i32>().into();

			// ^Delta(ms) = n
			let mut delta = KeyContext::new(&ctx, "^Delta", &[us.as_bytes()]);
			delta.set(n.to_string().as_bytes()).unwrap();

			// ^Crab(ms) = ^Crab(lasttime) - n
			let mut crab = KeyContext::new(&ctx, "^Crab", &[us.as_bytes()]);
			let mut last_crab = crab.prev_sub().unwrap();
			let last_crab_val: i64 = String::from_utf8_lossy(&last_crab.get().unwrap())
				.parse()
				.unwrap();
			crab.set((last_crab_val - n).to_string()).unwrap();

			// ^Horse(ms) = ^Horse(lasttime) + n
			let mut horse = KeyContext::new(&ctx, "^Horse", &[us]);
			let mut last_horse = horse.prev_sub().unwrap();
			let last_horse_val: i64 = String::from_utf8_lossy(&last_horse.get().unwrap())
				.parse()
				.unwrap();
			horse.set((last_horse_val + n).to_string()).unwrap();

			Ok(())
		}, "BATCH", &[]).unwrap();
		std::thread::sleep(Duration::from_millis(500));
	}
}

fn verify() {
    use std::process;
    use yottadb::craw::YDB_ERR_NODEEND;

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
