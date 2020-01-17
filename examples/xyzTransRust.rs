#![allow(non_snake_case)]

//! Update a multi-region database using ACID transactions
//! This program is part of the exercises in the YottaDB Acculturation Workshop at
//! https://docs.yottadb.com/AcculturationGuide/acculturation.html
//! and its use is discussed there.
//!
//! For the sake of simplicity, this program does no error handling.
use std::time::{Duration, SystemTime};

use rand::Rng;
use yottadb::context_api::{Context, KeyContext};

fn main() {
	let mut rng = rand::thread_rng();
	let ctx = Context::new();

	loop {
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
