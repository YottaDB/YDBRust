//! Rust implementation of the 3n+1 problem
//! https://yottadb.com/solving-the-3n1-problem-with-yottadb/

#[macro_use]
extern crate yottadb;
extern crate num_cpus;
extern crate threadpool;

use std::error::Error;
use std::io::{self, BufRead};
use std::sync::{Arc, Barrier};
use std::time::SystemTime;

use threadpool::ThreadPool;
use yottadb::context_api::Context;
use yottadb::{YDB_ERR_GVUNDEF, DeleteType, DataReturn, TransactionStatus, YDBError};

fn main() -> Result<(), Box<dyn Error>> {
    let ctx = Context::new();

    // Clear out old values
    let mut limits = make_ckey!(ctx, "^limits");
    limits.delete(DeleteType::DelTree)?;
    let result = make_ckey!(ctx, "^result");
    result.delete(DeleteType::DelTree)?;
    let highest = make_ckey!(ctx, "^highest");
    highest.delete(DeleteType::DelTree)?;
    let updates = make_ckey!(ctx, "^updates");
    updates.delete(DeleteType::DelTree)?;
    let reads = make_ckey!(ctx, "^reads");
    reads.delete(DeleteType::DelTree)?;
    let mut step = make_ckey!(ctx, "^step");
    step.delete(DeleteType::DelTree)?;

    let cpus = num_cpus::get();
    let stdin = io::stdin();
    for line in stdin.lock().lines() {
        let line = line?;
        let tokens: Vec<usize> =
            line.split_whitespace().map(|x| x.parse::<usize>().unwrap()).collect();
        let (endnum, streams, mut blk) = match tokens.as_slice() {
            &[] => (0, cpus * 2, 0),
            &[endnum] => (endnum, cpus * 2, 0),
            &[endnum, streams] => (endnum, streams, 0),
            &[endnum, streams, blk] => (endnum, streams, blk),
            _ => panic!("Too many parameters passed!"),
        };

        print!(" endnum={} streams={}", endnum, streams);
        let maxblk = (endnum + (streams - 1)) / streams;
        if blk != 0 && blk <= maxblk {
            print!(" blk={}", blk);
        } else {
            print!(" blk=({}->{})", blk, maxblk);
            blk = maxblk;
        }
        // Kill all limits again for this run
        limits.clear();
        limits.delete(DeleteType::DelTree)?;
        limits.push(Vec::new());

        // Reset globals
        highest.set(b"0")?;
        reads.set(b"0")?;
        result.set(b"0")?;
        updates.set(b"0")?;
        step.clear();
        step.delete(DeleteType::DelTree)?;

        // Set limits for each block to be computed, letting each thread grab
        // a ^limits(i) when it starts or finishes a block
        let mut i = 0;
        let mut tmp = 0;
        loop {
            if tmp == endnum {
                break;
            }
            tmp += blk;
            if tmp > endnum {
                tmp = endnum;
            }
            limits[0] = Vec::from(i.to_string());
            limits.set(&Vec::from(tmp.to_string()))?;
            i += 1;
        }

        // Create the threadpool and launch workers
        let threadpool = ThreadPool::new(streams);
        // +1 since the main thread will "kick them off" all at once;
        // this is sorta  a no-op, but consistent with other implementations
        let start_barrier = Arc::new(Barrier::new(streams + 1));
        let end_barrier = Arc::new(Barrier::new(streams + 1));
        for i in 0..streams {
            let start_barrier = start_barrier.clone();
            let end_barrier = end_barrier.clone();

            threadpool.execute(move || {
                start_barrier.wait();

                // Do work
                doblk(i).unwrap();

                // Mark ourselves done
                end_barrier.wait();
            });
        }

        // Release the threads!
        start_barrier.wait();
        let start_time = SystemTime::now();
        // Wait for them to finish
        end_barrier.wait();
        let time = match start_time.elapsed() {
            Ok(elapsed) => elapsed.as_millis(),
            Err(x) => panic!(x),
        } as f64;

        let updt = updates.get()?;
        let updt = String::from_utf8_lossy(&updt);
        let res = result.get()?;
        let res = String::from_utf8_lossy(&res);
        let high = highest.get()?;
        let high = String::from_utf8_lossy(&high);
        let red = reads.get()?;
        let red = String::from_utf8_lossy(&red);
        print!(
            " result={} highest={} time={} updates={} reads={}",
            res,
            high,
            time / 1000.0,
            updt,
            red
        );
        let updatecnt = updt.parse::<u64>()? as f64;
        let readcnt = red.parse::<u64>()? as f64;

        if time > 0.0 {
            print!(
                " updates/s={} reads/s={}",
                updatecnt / (time / 1000.0),
                readcnt / (time / 1000.0)
            );
        }
        println!();
    }

    Ok(())
}

fn doblk(index: usize) -> Result<(), Box<dyn Error>> {
    let mut index = index;
    let ctx = Context::new();
    let reads = make_ckey!(ctx, "^reads");
    let updates = make_ckey!(ctx, "^updates");
    let highest = make_ckey!(ctx, "^highest");
    let mut limits = make_ckey!(ctx, "^limits", "1", "");
    let mut step = make_ckey!(ctx, "^step", "1");
    let result = make_ckey!(ctx, "^result");

    // Local to prevent collisions until engine is fully multithreaded
    let index_s = index.to_string();
    let updates_l = make_ckey!(ctx, "updates", index_s.clone());
    updates_l.set(b"0")?;
    let reads_l = make_ckey!(ctx, "reads", index_s.clone());
    reads_l.set(b"0")?;
    let highest_l = make_ckey!(ctx, "highest", index_s.clone());
    highest_l.set(b"0")?;
    let mut currpath_l = make_ckey!(ctx, "currpath", index_s.as_str(), "");

    loop {
        index += 1;
        limits.truncate(1);
        limits[0] = Vec::from(index.to_string());
        // If there are no more elements left in limits, we are done
        let data = limits.data()?;
        if data == DataReturn::NoData {
            break;
        }
        limits.push(Vec::from("1"));
        let val = limits.increment(None)?;
        // If we didn't get a value of 1, someone else has this block to work on
        if val != Vec::from("1") {
            continue;
        }
        limits.truncate(1);
        let val = limits.get()?;
        let blkend = String::from_utf8_lossy(&val);
        let blkend = blkend.parse::<u64>()?;
        let blkstart = if index == 1 {
            1
        } else {
            limits[0] = Vec::from((index - 1).to_string());
            let v = limits.get()?;
            let v = String::from_utf8_lossy(&v);
            v.parse::<u64>()? + 1
        };

        // Logic from dostep in other versions here; not sure why it's a function at this point
        for current in blkstart..=blkend {
            let mut n = current;
            currpath_l.truncate(1);
            currpath_l.delete(DeleteType::DelTree)?;
            currpath_l.push(Vec::new());
            let mut i = 0;
            loop {
                reads_l.increment(None)?;
                step[0] = Vec::from(n.to_string());
                let dval = step.data()?;
                if dval != DataReturn::NoData || n == 1 {
                    break;
                }
                currpath_l[1] = Vec::from(i.to_string());
                currpath_l.set(&Vec::from(n.to_string()))?;
                n = if n % 2 == 0 { n / 2 } else { 3 * n + 1 };
                let highest_v = highest_l.get()?;
                let highest_v = String::from_utf8_lossy(&highest_v);
                let highest_v = highest_v.parse::<u64>()?;
                if n > highest_v {
                    highest_l.set(&Vec::from(n.to_string()))?;
                }
                i += 1;
            }

            if i > 0 {
                if n > 1 {
                    step[0] = Vec::from(n.to_string());
                    let add_steps = step.get()?;
                    let add_steps = String::from_utf8_lossy(&add_steps);
                    let add_steps = add_steps.parse::<u64>()?;
                    i += add_steps;
                }
                ctx.tp(|_ctx| {
                    let result_v = match result.get() {
                        Ok(x) => x,
                        Err(YDBError { status: YDB_ERR_GVUNDEF, .. }) => Vec::from("0"),
                        Err(x) => return Err(Box::new(x)),
                    };
                    let result_v = String::from_utf8_lossy(&result_v);
                    let result_v = result_v.parse::<u64>()?;
                    if result_v < i {
                        result.set(&Vec::from(i.to_string()))?;
                    }
                    Ok(TransactionStatus::Ok)
                }, "BATCH", &Vec::new())?;
                currpath_l[1] = Vec::from("");
                for subval in currpath_l.iter_subs_values() {
                    let (sub, val) = subval?;
                    let n = String::from_utf8_lossy(&sub);
                    let n = n.parse::<u64>()?;
                    updates_l.increment(None)?;
                    step[0] = val;
                    step.set(&Vec::from((i - n).to_string()))?;
                }
            }
        }
    }

    // Update values for total reads, total writes, and highest
    ctx.tp(|_ctx| {
        reads.increment(Some(&reads_l.get()?))?;
        updates.increment(Some(&updates_l.get()?))?;
        let high = match highest.get() {
            Ok(x) => x,
            Err(YDBError { status: YDB_ERR_GVUNDEF, .. }) => Vec::from("0"),
            Err(x) => return Err(Box::new(x)),
        };
        let high = String::from_utf8_lossy(&high);
        let high = high.parse::<u64>()?;
        let high_l = highest_l.get()?;
        let high_l = String::from_utf8_lossy(&high_l);
        let high_l = high_l.parse::<u64>()?;
        if high < high_l {
            highest.set(&Vec::from(high_l.to_string()))?;
        }
        Ok(TransactionStatus::Ok)
    }, "BATCH", &Vec::new())?;

    Ok(())
}
