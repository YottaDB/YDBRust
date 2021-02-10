/****************************************************************
*                                                               *
* Copyright (c) 2021 YottaDB LLC and/or its subsidiaries.  *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

use proptest::prelude::*;
use crate::*;
use crate::test_lock::LockGuard;
use super::*;

fn arb_key() -> impl Strategy<Value = Key> {
    any::<(String, Vec<Vec<u8>>)>().prop_map(|(var, subs)| Key::new(var, &subs))
}

fn arb_keys() -> impl Strategy<Value = Vec<Key>> {
    proptest::collection::vec(arb_key(), 0..12)
}

#[test]
fn can_make_key() {
    Key::variable("key");
}

#[test]
fn can_make_key_with_subscripts() {
    Key::new("^hello", &["world"]);
}

#[test]
fn basic_set_and_get_st() {
    let _guard = LockGuard::read();

    let mut result = Vec::new();
    let key = Key::variable("^basicSetGet");

    // Try setting a value
    result = key.set_st(YDB_NOTTP, result, b"Hello world!").unwrap();
    // Then try getting the value we set
    result = key.get_st(YDB_NOTTP, result).unwrap();
    assert_eq!(result, b"Hello world!");

    // Try an error where the error message is shorter than the retrieved value
    let val: &[_] = &[b'a'; 1000];
    key.set_st(YDB_NOTTP, result, &val).unwrap();
    // Then try getting the value we set
    result = key.get_st(YDB_NOTTP, Vec::new()).unwrap();
    assert_eq!(result, val);
}

#[test]
fn ydb_get_st_error() {
    let _guard = LockGuard::read();

    let key = Key::variable("^helloDoesntExists");
    let err = key.get_st(YDB_NOTTP, Vec::new()).unwrap_err();
    assert_eq!(err.status, crate::craw::YDB_ERR_GVUNDEF);

    let key = Key::variable("helloDoesntExists");
    let err = key.get_st(YDB_NOTTP, Vec::new()).unwrap_err();
    assert_eq!(err.status, crate::craw::YDB_ERR_LVUNDEF);
}

#[test]
fn ydb_set_st_error() {
    let _guard = LockGuard::read();

    let key = Key::variable("$ZCHSET");
    let err = key.set_st(YDB_NOTTP, Vec::new(), "some val").unwrap_err();
    assert_eq!(err.status, craw::YDB_ERR_SVNOSET)
    // other errors tested in `common_errors`
}

#[test]
fn ydb_data_st() {
    let _guard = LockGuard::read();

    let err_buf = Vec::new();
    let mut key = Key::variable("testDataSt");

    // should be empty to start
    let (retval, err_buf) = key.data_st(YDB_NOTTP, err_buf).unwrap();
    assert_eq!(retval, DataReturn::NoData);

    // set the node
    let err_buf = key.set_st(YDB_NOTTP, err_buf, "some data").unwrap();
    let (retval, err_buf) = key.data_st(YDB_NOTTP, err_buf).unwrap();
    assert_eq!(retval, DataReturn::ValueData);

    // set node and child
    key.push("some subscript".into());
    let err_buf = key.set_st(YDB_NOTTP, err_buf, "subscript data").unwrap();
    key.pop();
    let (retval, err_buf) = key.data_st(YDB_NOTTP, err_buf).unwrap();
    assert_eq!(retval, DataReturn::ValueTreeData);

    // delete the node, keep the child
    let err_buf = key.delete_st(YDB_NOTTP, err_buf, DeleteType::DelNode).unwrap();
    let (retval, err_buf) = key.data_st(YDB_NOTTP, err_buf).unwrap();
    assert_eq!(retval, DataReturn::TreeData);

    // delete the tree
    let err_buf = key.delete_st(YDB_NOTTP, err_buf, DeleteType::DelTree).unwrap();
    let (retval, _) = key.data_st(YDB_NOTTP, err_buf).unwrap();
    assert_eq!(retval, DataReturn::NoData);
}

#[test]
fn ydb_delete_st() {
    let _guard = LockGuard::read();

    let mut result = Vec::new();
    let key = Key::variable("^helloDeleteMe");

    // Try setting a value
    result = key.set_st(YDB_NOTTP, result, b"Hello world!").unwrap();
    // Check data
    let (retval, mut result) = key.data_st(YDB_NOTTP, result).unwrap();
    assert_ne!(retval, DataReturn::NoData);
    // Delete the value
    result = key.delete_st(YDB_NOTTP, result, DeleteType::DelNode).unwrap();
    let (retval, _) = key.data_st(YDB_NOTTP, result).unwrap();
    // Check for no data
    assert_eq!(retval, DataReturn::NoData);
}

#[test]
fn ydb_delete_excl_st() {
    // This test cannot be run in parallel.
    let _guard = LockGuard::write();

    let out_buf = Vec::new();
    let mut key = Key::variable("deleteExcl");

    // Set a few values
    let out_buf = key.set_st(YDB_NOTTP, out_buf, b"some value").unwrap();
    key.variable = "deleteExcl2".into();
    let out_buf = key.set_st(YDB_NOTTP, out_buf, b"some value").unwrap();

    // Delete `deleteExcl2`, saving `deleteExcl`
    let out_buf = delete_excl_st(YDB_NOTTP, out_buf, &["deleteExcl"]).unwrap();
    // Check data
    let (data_type, out_buf) = key.data_st(YDB_NOTTP, out_buf).unwrap();
    assert_eq!(data_type, DataReturn::NoData);
    key.variable = "deleteExcl".into();
    let (data_type, out_buf) = key.data_st(YDB_NOTTP, out_buf).unwrap();
    assert_eq!(data_type, DataReturn::ValueData);

    // Delete `deleteExcl`
    let out_buf = delete_excl_st(YDB_NOTTP, out_buf, &[]).unwrap();
    // Make sure it was actually deleted
    let (data_type, out_buf) = key.data_st(YDB_NOTTP, out_buf).unwrap();
    assert_eq!(data_type, DataReturn::NoData);

    // Saving a global/intrinsic variable should be an error
    use crate::craw::YDB_ERR_INVVARNAME;
    let err = delete_excl_st(YDB_NOTTP, out_buf, &["^global"]).unwrap_err();
    assert_eq!(err.status, YDB_ERR_INVVARNAME);
    let err = delete_excl_st(YDB_NOTTP, Vec::new(), &["$ZSTATUS"]).unwrap_err();
    assert_eq!(err.status, YDB_ERR_INVVARNAME);

    // Saving a variable that doesn't exist should do nothing and return YDB_OK.
    delete_excl_st(YDB_NOTTP, Vec::new(), &["local"]).unwrap();

    // Check for `YDB_ERR_NAMECOUNT2HI` if too many params are passed
    use crate::craw::{YDB_ERR_NAMECOUNT2HI, YDB_MAX_NAMES};
    let vars = vec!["hello"; YDB_MAX_NAMES as usize + 1];
    let err = delete_excl_st(YDB_NOTTP, Vec::new(), &vars).unwrap_err();
    assert_eq!(err.status, YDB_ERR_NAMECOUNT2HI);

    // Passing a buffer that has insufficient capacity for an error should resize the buffer
    let err = delete_excl_st(YDB_NOTTP, Vec::new(), &["^global"]).unwrap_err();
    assert_eq!(err.status, YDB_ERR_INVVARNAME);
}

#[test]
fn ydb_incr_st() {
    let _guard = LockGuard::read();

    let err_buf = Vec::new();
    let key = Key::variable("^helloIncrementMe");
    let err_buf = key.set_st(YDB_NOTTP, err_buf, "0").unwrap();

    let err_buf = key.incr_st(YDB_NOTTP, err_buf, None).unwrap();
    let out_buf = key.get_st(YDB_NOTTP, err_buf).unwrap();
    assert_eq!(&out_buf, b"1");

    let num = 1500.to_string().into_bytes();
    let err_buf = key.incr_st(YDB_NOTTP, out_buf, Some(&num)).unwrap();
    let out_buf = key.get_st(YDB_NOTTP, err_buf).unwrap();
    assert_eq!(&out_buf, b"1501");

    // make sure that incr_st works even if the node doesn't exist yet
    let err_buf = key.delete_st(YDB_NOTTP, out_buf, DeleteType::DelNode).unwrap();
    let err_buf = key.incr_st(YDB_NOTTP, err_buf, None).unwrap();
    let out_buf = key.get_st(YDB_NOTTP, err_buf).unwrap();
    assert_eq!(&out_buf, b"1");

    // Make sure the value is converted when it isn't a number
    let err_buf = key.set_st(YDB_NOTTP, out_buf, "not a number").unwrap();
    let err_buf = key.incr_st(YDB_NOTTP, err_buf, None).unwrap();
    let out_buf = key.get_st(YDB_NOTTP, err_buf).unwrap();
    assert_eq!(&out_buf, b"1");

    // Clean up
    key.delete_st(YDB_NOTTP, out_buf, DeleteType::DelNode).unwrap();
}

// Return the number of locks held for `var`
pub(crate) fn lock_count(var: &str) -> usize {
    use std::os::raw::{c_char, c_ulong};
    use crate::craw::ydb_string_t;

    fn make_out_str_t(slice: &mut [u8]) -> ydb_string_t {
        ydb_string_t { address: slice.as_mut_ptr() as *mut c_char, length: slice.len() as c_ulong }
    }

    std::env::set_var("ydb_routines", "examples/m-ffi");
    std::env::set_var("ydb_ci", "examples/m-ffi/calltab.ci");

    let m_code = CString::new("zshvar").unwrap();
    let mut stored_var = Vec::from("outputvar");
    let mut output_var = Vec::from("l");
    let mut output_var_t = make_out_str_t(&mut output_var);
    let mut stored_var_t = make_out_str_t(&mut stored_var);

    let mut err_buf = unsafe {
        ci_t!(
            YDB_NOTTP,
            Vec::new(),
            &m_code,
            &mut output_var_t as *mut _,
            &mut stored_var_t as *mut _
        )
    }
    .unwrap();

    // look for the right key
    let mut count = 1;
    let mut key = Key::new(String::from_utf8(stored_var).unwrap(), &["L", "1"]);
    loop {
        let (data, loop_buf) = key.data_st(YDB_NOTTP, err_buf).unwrap();
        if data == DataReturn::NoData {
            return 0;
        }
        let val = key.get_st(YDB_NOTTP, loop_buf).unwrap();
        // looks like `LOCK x LEVEL=1`
        let locks = String::from_utf8(val).unwrap();
        let mut groups = locks.split_whitespace();
        assert_eq!(groups.next(), Some("LOCK"));
        let name = groups.next().unwrap();
        if name == var {
            let locks = groups.next().unwrap()["LEVEL=".len()..].parse().unwrap();
            assert_ne!(locks, 0);
            return locks;
        }
        count += 1;
        key[1] = count.to_string().into_bytes();
        err_buf = locks.into_bytes();
    }
}
#[test]
fn ydb_lock_incr_decr_st() {
    // This test cannot run in parallel with any others.
    let _guard = LockGuard::write();

    // Create a new lock
    let err_buf = Vec::new();
    let key = Key::variable("simpleIncrLock");
    // Increment it twice
    let err_buf = key.lock_incr_st(YDB_NOTTP, err_buf, Duration::from_millis(500)).unwrap();
    let err_buf = key.lock_incr_st(YDB_NOTTP, err_buf, Duration::from_secs(0)).unwrap();
    // Make sure the lock count is correct
    assert_eq!(lock_count(&key.variable), 2);

    // Decrement it twice
    let err_buf = key.lock_decr_st(YDB_NOTTP, err_buf).unwrap();
    key.lock_decr_st(YDB_NOTTP, err_buf).unwrap();
    // Make sure the lock has been released
    assert_eq!(lock_count(&key.variable), 0);

    // Test for TIME2LONG
    for &time in
        &[std::u64::MAX, std::u32::MAX.into(), (std::u32::MAX / 2).into(), 0xf00_0000_0000_0000]
    {
        let res = key.lock_incr_st(YDB_NOTTP, Vec::new(), Duration::from_secs(time));
        assert!(res.unwrap_err().status == craw::YDB_ERR_TIME2LONG);
    }
}

#[test]
fn ydb_lock_st() {
    use crate::craw::{YDB_ERR_MAXARGCNT, YDB_ERR_TIME2LONG};

    // This test cannot run in parallel with any others.
    let _guard = LockGuard::write();

    // Test global and local locks
    for &lock in &["ydbLock", "^ydbLock"] {
        let key = Key::variable(lock);
        assert_eq!(lock_count(&key.variable), 0);
        // Acquire the lock
        lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), std::slice::from_ref(&key)).unwrap();
        assert_eq!(lock_count(&key.variable), 1);
        // Release all locks
        lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), &[]).unwrap();
        assert_eq!(lock_count(&key.variable), 0);
    }

    // Test for too many locks
    let mut locks = Vec::new();
    for c in b'a'..=b'z' {
        let var = String::from_utf8([c].to_vec()).unwrap();
        locks.push(Key::variable(var));
    }
    let res = lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), &locks);
    assert!(res.unwrap_err().status == YDB_ERR_MAXARGCNT);

    // Test for TIME2LONG
    for &time in
        &[std::u64::MAX, std::u32::MAX.into(), (std::u32::MAX / 2).into(), 0xf00_0000_0000_0000]
    {
        let res = lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(time), &[]);
        assert!(res.unwrap_err().status == YDB_ERR_TIME2LONG);
    }

    // Test for the maximum number of locks
    locks.clear();
    #[cfg(target_pointer_width = "64")]
    let max = 10;
    #[cfg(target_pointer_width = "32")]
    let max = 9;
    for i in 0..max {
        // YDB variables can't start with a number
        let mut s = String::from("a");
        s.push_str(&i.to_string());
        locks.push(Key::variable(s));
    }
    lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), &locks).unwrap();
    for lock in &locks {
        assert_eq!(lock_count(&lock.variable), 1);
    }
    locks.push(Key::variable("oneTooMany"));
    let err = lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), &locks).unwrap_err();
    assert_eq!(err.status, YDB_ERR_MAXARGCNT);
}

#[test]
fn ydb_node_next_self_st() {
    let _guard = LockGuard::read();

    let mut result = Vec::new();
    let value = Vec::from("Hello world!");
    let mut key = make_key!("^helloNodeNext", "shire");
    result = key.set_st(YDB_NOTTP, result, &value).unwrap();
    key[0] = Vec::from("hyrule");
    result = key.set_st(YDB_NOTTP, result, &value).unwrap();
    key[0] = Vec::from("a");
    key.node_next_self_st(YDB_NOTTP, result).unwrap();
}

#[test]
fn ydb_node_next_self_extra_node_st() {
    let _guard = LockGuard::read();

    let mut result = Vec::new();
    let value = b"Hello world!";
    let mut key = make_key!("^helloNodeNext2", "worlds", "shire");
    result = key.set_st(YDB_NOTTP, result, value).unwrap();
    key[1] = Vec::from("hyrule");
    result = key.set_st(YDB_NOTTP, result, value).unwrap();
    key.truncate(2);
    key.node_next_self_st(YDB_NOTTP, result).unwrap();

    // YDB_ERR_NODEEND
    // make sure NODEEND is still returned if we call multiple times in a row
    for _ in 0..10 {
        let err = key.node_next_self_st(YDB_NOTTP, Vec::new()).unwrap_err();
        assert_eq!(err.status, craw::YDB_ERR_NODEEND);
    }

    // now test it for node_prev_self
    key.node_prev_self_st(YDB_NOTTP, Vec::new()).unwrap();
    assert_eq!(key[1], b"hyrule");
    for _ in 0..10 {
        let err = key.node_prev_self_st(YDB_NOTTP, Vec::new()).unwrap_err();
        assert_eq!(err.status, craw::YDB_ERR_NODEEND);
    }
}

#[test]
fn ydb_node_prev_self_st() {
    let _guard = LockGuard::read();

    let mut result = Vec::new();
    let value = Vec::from("Hello world!");
    let mut key = make_key!("^helloNodeprev", "shire");
    result = key.set_st(YDB_NOTTP, result, &value).unwrap();
    key[0] = Vec::from("hyrule");
    result = key.set_st(YDB_NOTTP, result, &value).unwrap();
    key[0] = Vec::from("z");
    if let Err(err) = key.node_prev_self_st(YDB_NOTTP, result) {
        panic!("{}", err);
    }
}

#[test]
fn ydb_node_prev_self_extra_node_st() {
    let _guard = LockGuard::read();

    let mut result = Vec::new();
    let value = Vec::from("Hello world!");
    let mut key = make_key!("^helloNodeprev2", "worlds", "shire");
    result = key.set_st(YDB_NOTTP, result, &value).unwrap();
    key[1] = Vec::from("hyrule");
    result = key.set_st(YDB_NOTTP, result, &value).unwrap();
    key.truncate(2);
    key[0] = Vec::from("z");
    key.node_prev_self_st(YDB_NOTTP, result).unwrap();
}

#[test]
fn ydb_subscript_next() {
    let _guard = LockGuard::read();

    let mut result = Vec::new();
    let mut key = make_key!("^helloSubNext", "a");
    result = key.set_st(YDB_NOTTP, result, b"Hello world!").unwrap();
    key[0] = Vec::new();
    result = key.sub_next_st(YDB_NOTTP, result).unwrap();
    assert_eq!(result, b"a");
    key[0] = vec![b'a'];
    key.delete_st(YDB_NOTTP, Vec::new(), DeleteType::DelNode).unwrap();

    key[0] = vec![b'a'; 100];
    key.delete_st(YDB_NOTTP, Vec::new(), DeleteType::DelNode).unwrap();

    // Test a subscript with an INVSTRLEN shorter than the required capacity
    key[0] = vec![b'a'; 150];
    key.set_st(YDB_NOTTP, result, "some val").expect("set_st");

    key[0] = vec![b'a'];
    let subs = key.sub_next_st(YDB_NOTTP, Vec::new()).expect("sub_next");
    assert_eq!(subs.as_slice(), &[b'a'; 150][..]);

    key[0] = vec![b'b'];
    let subs = key.sub_prev_st(YDB_NOTTP, Vec::new()).expect("sub_prev");
    assert_eq!(subs.as_slice(), &[b'a'; 150][..]);
    key[0] = subs;
    key.delete_st(YDB_NOTTP, Vec::new(), DeleteType::DelTree).unwrap();
}

#[test]
fn ydb_subscript_prev() {
    let _guard = LockGuard::read();

    let mut result = Vec::new();
    let value = Vec::from("Hello world!");
    let mut key = make_key!("^helloSubprev", "b");
    result = key.set_st(YDB_NOTTP, result, &value).unwrap();
    key[0] = Vec::from("z");
    result = key.sub_prev_st(YDB_NOTTP, result).unwrap();
    assert_eq!(result, Vec::from("b"));
}

#[test]
fn ydb_subscript_next_self() {
    let _guard = LockGuard::read();

    let mut result = Vec::new();
    let value = Vec::from("Hello world!");
    let mut key = make_key!("^helloSubNext2", "shire");
    result = key.set_st(YDB_NOTTP, result, &value).unwrap();
    // TODO: we need a better way to expand these buffers in the _self function
    key[0] = Vec::new();
    key.sub_next_self_st(YDB_NOTTP, result).unwrap();
    assert_eq!(key[0], Vec::from("shire"));
}

#[test]
fn ydb_subscript_prev_self() {
    let _guard = LockGuard::read();

    let mut result = Vec::new();
    let value = Vec::from("Hello world!");
    let mut key = make_key!("^helloSubprev2", "shire");
    result = key.set_st(YDB_NOTTP, result, &value).unwrap();
    key[0] = Vec::from("z");
    key.sub_prev_self_st(YDB_NOTTP, result).unwrap();
    assert_eq!(key[0], Vec::from("shire"));
}

#[test]
fn ydb_tp_st() {
    use crate::craw;

    let _guard = LockGuard::read();

    // Variables are persisted after a transaction
    let key = Key::variable("tpPersistence");
    let result = Vec::new();
    let result = tp_st(
        YDB_NOTTP,
        result,
        |tptoken| {
            key.set_st(tptoken, Vec::new(), "value").unwrap();
            Ok(TransactionStatus::Ok)
        },
        "BATCH",
        &[],
    )
    .unwrap();
    assert_eq!(key.get_st(YDB_NOTTP, Vec::new()).unwrap(), b"value");

    // user error
    let err = tp_st(YDB_NOTTP, result, |_| Err("oops!".into()), "BATCH", &[]).unwrap_err();
    assert_eq!(err.to_string(), "oops!");

    // ydb error
    let vec = Vec::new();
    let err = tp_st(
        YDB_NOTTP,
        vec,
        |tptoken| {
            let key = make_key!("hello");
            key.get_st(tptoken, Vec::new())?;
            unreachable!();
        },
        "BATCH",
        &[],
    )
    .unwrap_err();
    assert!(err.downcast::<YDBError>().unwrap().status == craw::YDB_ERR_LVUNDEF);

    // TPTOODEEP
    fn call_forever(tptoken: TpToken) -> UserResult {
        tp_st(tptoken, Vec::new(), call_forever, "BATCH", &[])?;
        Ok(TransactionStatus::Ok)
    }
    let err = call_forever(YDB_NOTTP).unwrap_err();
    match &err.downcast::<YDBError>() {
        Ok(ydb_err) if ydb_err.status == craw::YDB_ERR_TPTOODEEP => {}
        other => panic!("expected ERR_TPTOODEEP, got {:?}", other),
    }

    // Check for `YDB_ERR_NAMECOUNT2HI` if too many params are passed
    let vars = vec!["hello"; craw::YDB_MAX_NAMES as usize + 1];
    let err =
        tp_st(YDB_NOTTP, Vec::new(), |_| Ok(TransactionStatus::Ok), "BATCH", &vars).unwrap_err();
    match err.downcast::<YDBError>() {
        Ok(err) => assert_eq!(err.status, craw::YDB_ERR_NAMECOUNT2HI),
        other => panic!("expected ERR_TPTOODEEP, got {:?}", other),
    }

    // Check that TLEVEL is set properly
    let tlevel = Key::variable("$TLEVEL");
    assert_eq!(&tlevel.get_st(YDB_NOTTP, Vec::new()).unwrap(), b"0");
    tp_st(
        YDB_NOTTP,
        Vec::new(),
        |tptoken| {
            let val = tlevel.get_st(tptoken, Vec::new()).unwrap();
            assert_eq!(&val, b"1");
            Ok(TransactionStatus::Ok)
        },
        "BATCH",
        &[],
    )
    .unwrap();
    assert_eq!(&tlevel.get_st(YDB_NOTTP, Vec::new()).unwrap(), b"0");
}

#[test]
fn nested_transaction() {
    let _guard = LockGuard::read();

    let mut first_run = true;
    tp_st(
        YDB_NOTTP,
        Vec::new(),
        |tptoken| {
            // Save this value because it's about to change
            let captured_first_run = first_run;
            // Some inner transaction that returns a RESTART
            // The restart is propagated upward by the `?`,
            // since `tp_st` returns YDBError { status: YDB_TP_RESTART }.
            let res = tp_st(
                tptoken,
                Vec::new(),
                |_| {
                    if first_run {
                        first_run = false;
                        Ok(TransactionStatus::Restart)
                    } else {
                        Ok(TransactionStatus::Ok)
                    }
                },
                "BATCH",
                &[],
            );
            // Make sure `RESTART` is returned the first time
            if captured_first_run {
                let err = res.unwrap_err();
                let status = err.downcast_ref::<YDBError>().unwrap().status;
                assert_eq!(status, YDB_TP_RESTART);
                Err(err)
            } else {
                // Make sure `OK` is return the second time
                res.unwrap();
                Ok(TransactionStatus::Ok)
            }
        },
        "BATCH",
        &[],
    )
    .unwrap();
}

#[test]
fn restart_resets_locals() {
    // This test cannot run in parallel with any others.
    let _guard = LockGuard::write();
    let a = Key::variable("tpResetsLocals");

    for locals in &[&["*"][..], &[a.variable.as_str()], &[&a.variable, "b", "c"]] {
        let mut i = 0;

        a.set_st(YDB_NOTTP, Vec::new(), "initial value").unwrap();
        assert_eq!(&a.get_st(YDB_NOTTP, Vec::new()).unwrap(), b"initial value");

        // make sure `a` is reset after each call
        let closure = |tptoken| {
            assert_eq!(&a.get_st(tptoken, Vec::new()).unwrap(), b"initial value");
            a.set_st(tptoken, Vec::new(), "new value").unwrap();
            assert_eq!(&a.get_st(tptoken, Vec::new()).unwrap(), b"new value");
            if i == 3 {
                Ok(TransactionStatus::Ok)
            } else {
                i += 1;
                Ok(TransactionStatus::Restart)
            }
        };
        tp_st(YDB_NOTTP, Vec::new(), closure, "BATCH", locals).unwrap();
    }

    // now make sure that locals are not reset unless specified
    for locals in &[&["b"][..], &["b", "c", "d"], &[]] {
        a.set_st(YDB_NOTTP, Vec::new(), "initial value").unwrap();
        assert_eq!(&a.get_st(YDB_NOTTP, Vec::new()).unwrap(), b"initial value");

        let mut i = 0;
        tp_st(
            YDB_NOTTP,
            Vec::new(),
            |tptoken| {
                if i == 0 {
                    assert_eq!(&a.get_st(tptoken, Vec::new()).unwrap(), b"initial value");
                } else {
                    assert_eq!(&a.get_st(tptoken, Vec::new()).unwrap(), b"new value");
                }
                a.set_st(tptoken, Vec::new(), "new value").unwrap();
                assert_eq!(&a.get_st(tptoken, Vec::new()).unwrap(), b"new value");
                if i == 3 {
                    Ok(TransactionStatus::Ok)
                } else {
                    i += 1;
                    Ok(TransactionStatus::Restart)
                }
            },
            "BATCH",
            locals,
        )
        .unwrap();
    }
}

#[test]
fn rollback() {
    let _guard = LockGuard::read();

    let key = Key::variable("^tpRollbackTest");
    key.set_st(YDB_NOTTP, Vec::new(), "initial").unwrap();
    let set_inner = |tptoken| {
        key.set_st(tptoken, Vec::new(), "val")?;
        Ok(TransactionStatus::Rollback)
    };
    let err = tp_st(YDB_NOTTP, Vec::new(), set_inner, "BATCH", &[]).unwrap_err();
    let status = err.downcast::<YDBError>().unwrap().status;
    assert_eq!(status, craw::YDB_TP_ROLLBACK);
    assert_eq!(key.get_st(YDB_NOTTP, Vec::new()).unwrap(), b"initial");
}

#[test]
#[should_panic]
fn panic_in_cb() {
    tp_st(YDB_NOTTP, Vec::new(), |_| panic!("oh no!"), "BATCH", &[]).unwrap_err();
}

#[test]
fn ydb_message_t() {
    use crate::craw;

    let _guard = LockGuard::read();

    let mut err =
        YDBError { message: Vec::new(), status: craw::YDB_ERR_GVUNDEF, tptoken: YDB_NOTTP };
    assert!(err.to_string().contains("%YDB-E-GVUNDEF, Global variable undefined"));

    // make sure it works even if it has to resize the out_buffer
    err.status = 150380370;
    let expected = "%YDB-E-INVTRNSQUAL, Invalid TRANSACTION qualifier.  Specify only one of TRANSACTION=[NO]SET or TRANSACTION=[NO]KILL.";
    assert!(err.to_string().contains(expected), "expected INVTRNSQUAL, got {}", err.to_string());

    err.status = 10001;
    assert!(err.to_string().contains("%SYSTEM-E-ENO10001, Unknown error 10001"));
}

proptest::proptest! {
    #[test]
    fn ydb_zwr2str_st_proptest(s in ".*") {
        let serialized = str2zwr_st(YDB_NOTTP, Vec::new(), s.as_bytes()).unwrap();
        let deserialized = zwr2str_st(YDB_NOTTP, Vec::new(), &serialized).unwrap();
        assert_eq!(s.as_bytes(), deserialized.as_slice());
    }
    #[test]
    fn ydb_zwr2str_st_bytes_proptest(s: Vec<u8>) {
        let serialized = str2zwr_st(YDB_NOTTP, Vec::new(), &s).unwrap();
        let deserialized = zwr2str_st(YDB_NOTTP, Vec::new(), &serialized).unwrap();
        assert_eq!(s, deserialized);
    }
    #[test]
    fn no_invlnpairlist_lock_proptest(timeout: Duration, keys in arb_keys()) {
        // lock_st should never return `INVLNPAIRLIST`
        match lock_st(YDB_NOTTP, Vec::new(), timeout, &keys) {
            Err(YDBError { status: craw::YDB_ERR_INVLNPAIRLIST, .. }) => panic!("lock_st should never return YDB_ERR_INVLNPAIRLIST"),
            _ => {}
        }
    }
    #[test]
    // no Rust Simple API should ever return INVSTRLEN or INSUFFSUBS
    fn no_invalid_errors_proptest(key in arb_key(), value: Vec<u8>, b: bool) {
        fn assert_not_invalid<T>(res: YDBResult<T>) {
            match res {
                Err(YDBError { status: YDB_ERR_INVSTRLEN, .. }) => {
                    panic!("function returned YDB_ERR_INVSTRLEN");
                }
                Err(YDBError { status: YDB_ERR_INSUFFSUBS, .. }) => {
                    panic!("function returned YDB_ERR_INVSTRLEN");
                }
                _ => {}
            };
        }
        let tptoken = YDB_NOTTP;
        assert_not_invalid(key.get_st(tptoken, vec![]));
        assert_not_invalid(key.set_st(tptoken, vec![], &value));
        assert_not_invalid(key.data_st(tptoken, vec![]));
        assert_not_invalid(key.delete_st(tptoken, vec![], if b { DeleteType::DelTree } else { DeleteType::DelNode }));
        assert_not_invalid(key.incr_st(tptoken, vec![], if b { Some(&value) } else { None }));
        assert_not_invalid(key.lock_incr_st(tptoken, vec![], Duration::from_secs(0)));
        assert_not_invalid(key.lock_decr_st(tptoken, vec![]));
        assert_not_invalid(key.clone().node_next_self_st(tptoken, vec![]));
        assert_not_invalid(key.clone().node_prev_self_st(tptoken, vec![]));
        assert_not_invalid(key.clone().sub_next_st(tptoken, vec![]));
        assert_not_invalid(key.clone().sub_prev_st(tptoken, vec![]));
    }
}

#[test]
fn ydb_zwr2str_st() {
    let s = "hello good morning this is a very very long string that you'll have to resize";
    let serialized = str2zwr_st(YDB_NOTTP, Vec::new(), s.as_bytes()).unwrap();
    let deserialized = zwr2str_st(YDB_NOTTP, Vec::new(), &serialized).unwrap();
    assert_eq!(s.as_bytes(), deserialized.as_slice());

    // found by proptest
    let s = "🕴\'\u{c3d07}\u{106179}\u{1b}\u{a8c00}\u{c41b6}";
    println!("{}", s.len());
    let serialized = str2zwr_st(YDB_NOTTP, Vec::new(), s.as_bytes()).unwrap();
    let deserialized = zwr2str_st(YDB_NOTTP, Vec::new(), &serialized).unwrap();
    assert_eq!(s.as_bytes(), deserialized.as_slice());
}

#[test]
fn empty_err_buf() {
    use crate::craw::YDB_ERR_GVUNDEF;

    let _guard = LockGuard::read();

    let key = Key::variable("^doesnotexist");
    let err_buf = Vec::new();
    let res = key.get_st(YDB_NOTTP, err_buf);
    assert_eq!(res.unwrap_err().status, YDB_ERR_GVUNDEF);
}
#[test]
fn empty_subscript() {
    use crate::craw::YDB_ERR_LVUNDEF;

    let _guard = LockGuard::read();

    let mut key = make_key!("simpleHello", "world");
    let err_buf = Vec::new();
    let err_buf = key.set_st(YDB_NOTTP, err_buf, "data").unwrap();
    key[0].clear();

    let err = key.get_st(YDB_NOTTP, Vec::new()).unwrap_err();
    assert_eq!(err.status, YDB_ERR_LVUNDEF);

    let err_buf = key.node_next_self_st(YDB_NOTTP, err_buf).unwrap();
    assert_eq!(&key[0], b"world");
    assert_eq!(&key.get_st(YDB_NOTTP, err_buf).unwrap(), b"data");
}

// https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-codes
// NOTE: if one of these tests fails, you can use
// `RUST_BACKTRACE=1 cargo test --lib common_errors` to find out which.
#[test]
fn common_errors() {
    let _guard = LockGuard::read();

    let expect_err_with = |key: Key, err_code, get| {
        // data_st
        let err = key.data_st(YDB_NOTTP, Vec::new()).unwrap_err();
        assert_eq!(err.status, err_code);

        // delete_st
        let err = key.delete_st(YDB_NOTTP, Vec::new(), DeleteType::DelNode).unwrap_err();
        assert_eq!(err.status, err_code);

        // incr_st
        let err = key.incr_st(YDB_NOTTP, Vec::new(), None).unwrap_err();
        assert_eq!(err.status, err_code);

        // get_st
        if get {
            let err = key.get_st(YDB_NOTTP, Vec::new()).unwrap_err();
            assert_eq!(err.status, err_code);

            let err = key.set_st(YDB_NOTTP, Vec::new(), b"some val").unwrap_err();
            assert_eq!(err.status, err_code);
        }

        // lock_st
        let slice = std::slice::from_ref(&key);
        let res = lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(0), slice);
        assert_eq!(res.unwrap_err().status, err_code);

        // lock_incr_st
        let err = key.lock_incr_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1)).unwrap_err();
        assert_eq!(err.status, err_code);

        // lock_decr_st
        let err = key.lock_decr_st(YDB_NOTTP, Vec::new()).unwrap_err();
        assert_eq!(err.status, err_code);

        // node_next_st
        let mut dup = key.clone();
        let err = dup.node_next_self_st(YDB_NOTTP, Vec::new()).unwrap_err();
        assert_eq!(err.status, err_code);

        // node_prev_st
        let mut dup = key.clone();
        let err = dup.node_prev_self_st(YDB_NOTTP, Vec::new()).unwrap_err();
        assert_eq!(err.status, err_code);

        // sub_next_st
        let mut dup = key.clone();
        let err = dup.sub_next_self_st(YDB_NOTTP, Vec::new()).unwrap_err();
        assert_eq!(err.status, err_code);

        // sub_prev_st
        let mut dup = key.clone();
        let err = dup.sub_prev_self_st(YDB_NOTTP, Vec::new()).unwrap_err();
        assert_eq!(err.status, err_code);
    };
    let expect_err = |varname, err_code, get| {
        expect_err_with(Key::variable(varname), err_code, get);
    };
    expect_err("^", craw::YDB_ERR_INVVARNAME, true);
    expect_err("1", craw::YDB_ERR_INVVARNAME, true);
    expect_err("a_b_c", craw::YDB_ERR_INVVARNAME, true);
    expect_err("$ZCHSET", craw::YDB_ERR_UNIMPLOP, false);
    expect_err("$NOTANINTRINSIC", craw::YDB_ERR_INVSVN, true);
    expect_err(
        "^ThisIsAVeryLongVariableNameWithFarTooManyLetters",
        craw::YDB_ERR_VARNAME2LONG,
        true,
    );

    let subscripts: Vec<_> = (1..100).map(|i| i.to_string().into_bytes()).collect();
    let too_many_subscripts = Key::new("^somevar", &subscripts);
    expect_err_with(too_many_subscripts, craw::YDB_ERR_MAXNRSUBSCRIPTS, true);
}

#[test]
fn increment_errors() {
    let _guard = LockGuard::read();

    let key = Key::variable("incrementError");
    let err_buf = Vec::new();
    let err_buf = key.set_st(YDB_NOTTP, err_buf, "9E46").unwrap();
    let err = key.incr_st(YDB_NOTTP, err_buf, Some(b"1E46")).unwrap_err();
    assert_eq!(err.status, crate::craw::YDB_ERR_NUMOFLOW);
}
#[test]
fn undef_var() {
    use crate::craw::{YDB_ERR_GVUNDEF, YDB_ERR_LVUNDEF};

    let _guard = LockGuard::read();

    let key = Key::variable("^doesnotexist");
    let err_buf = Vec::new();
    let res = key.get_st(YDB_NOTTP, err_buf);
    assert_eq!(res.unwrap_err().status, YDB_ERR_GVUNDEF);

    let key = Key::variable("doesnotexist");
    let err_buf = Vec::new();
    let res = key.get_st(YDB_NOTTP, err_buf);
    assert_eq!(res.unwrap_err().status, YDB_ERR_LVUNDEF);
}

#[test]
fn release() {
    let version = dbg!(release_t(YDB_NOTTP, Vec::new()).unwrap());
    let mut parts = version.split_whitespace();
    assert_eq!(parts.next(), Some("rustwr"));
    assert_eq!(parts.next(), Some(env!("CARGO_PKG_VERSION")));
    assert_eq!(parts.next(), Some("YottaDB"));
    assert_eq!(&parts.next().unwrap()[0..1], "r");
    assert_eq!(parts.count(), 2);
}

#[test]
fn variable_reallocated() {
    let mut key = Key::variable(String::from("a"));
    dbg!(key.variable.capacity());
    Key::variable("averylongkeywithlotsofletters")
        .set_st(YDB_NOTTP, Vec::new(), b"some val")
        .unwrap();
    key.sub_next_self_st(YDB_NOTTP, Vec::new()).unwrap();
    dbg!(key.variable.capacity());
}

#[test]
fn error_buffer() {
    let mut inner_message = None;
    let err = tp_st(
        YDB_NOTTP,
        Vec::new(),
        |inner_tptoken| {
            let err = Key::variable("invalid_value")
                .set_st(inner_tptoken, Vec::new(), "new value")
                .unwrap_err();
            inner_message = Some(err.message.clone());
            return Err(Box::new(err));
        },
        "BATCH",
        &[],
    )
    .err()
    .expect("should have returned YDB_ERR_INVVARNAME");
    let ydb_err = err.downcast::<YDBError>().unwrap();
    // This should have the tptoken of the *outer* transaction, not the inner one.
    assert_eq!(ydb_err.tptoken, YDB_NOTTP);
    assert_eq!(ydb_err.message, inner_message.unwrap());
    println!("{}", String::from_utf8_lossy(&ydb_err.message));
}

#[test]
fn ydb_node_st_infinite_inv_str() {
    use crate::context_api::{Context, KeyContext};

    // `set ^x(1)=aaaaa,^x(2)=bbbbb`
    let ctx = Context::new();
    let mut key = KeyContext::new(&ctx, "x", &["1"]);
    key.set("a".repeat(DEFAULT_CAPACITY + 1)).unwrap();
    key[0] = "2".into();
    key.set("b".repeat(DEFAULT_CAPACITY + 1)).unwrap();
    // Make sure we don't use this by accident later
    drop(key);

    // Go to the end of the nodes
    let mut iter_key = Key::variable("x");
    iter_key.node_next_self_st(YDB_NOTTP, Vec::with_capacity(5)).unwrap();
    assert_eq!(
        iter_key[0],
        b"1",
        "{0}({1}) != {0}(1)",
        iter_key.variable,
        String::from_utf8_lossy(&iter_key[0])
    );
    iter_key.node_next_self_st(YDB_NOTTP, Vec::with_capacity(5)).unwrap();
    assert_eq!(iter_key[0], b"2");

    // Check for YDB_ERR_NODEEND
    // NOTE: this has knowledge of how the `simple_api` works internally.
    // If the vec has _any_ non-zero capacity, it will not be resized.
    let err = iter_key.node_next_self_st(YDB_NOTTP, Vec::with_capacity(1)).unwrap_err();
    assert_eq!(err.status, craw::YDB_ERR_NODEEND);
    eprintln!("{}", String::from_utf8(err.message).unwrap());

    // Check for YDB_ERR_INVVARNAME
    iter_key.variable = "a_b_c".to_string();
    let err = iter_key.node_next_self_st(YDB_NOTTP, Vec::with_capacity(1)).unwrap_err();
    assert_eq!(err.status, craw::YDB_ERR_INVVARNAME);
    eprintln!("{}", String::from_utf8(err.message).unwrap());
}

#[test]
fn sub_next_equivalent() {
    // set up a node with data at `subNextSelfUser("b")`
    let mut user = Key::new("subNextSelfUser", &["b"]);
    user.set_st(TpToken::default(), Vec::new(), b"Hello").unwrap();

    user[0] = "a".into();
    user[0] = user.sub_next_st(TpToken::default(), Vec::new()).unwrap();

    let mut ydb = Key::new("subNextSelfUser", &["a"]);
    ydb.sub_next_self_st(TpToken::default(), Vec::new()).unwrap();

    assert_eq!(user[0], ydb[0]);
}

#[test]
fn sub_prev_equivalent() {
    // set up a node with data at `subPrevSelfUser("a")`
    let mut user = Key::new("subPrevSelfUser", &["a"]);
    user.set_st(TpToken::default(), Vec::new(), b"Hello").unwrap();

    user[0] = "b".into();
    user[0] = user.sub_prev_st(TpToken::default(), Vec::new()).unwrap();

    let mut ydb = Key::new("subPrevSelfUser", &["b"]);
    ydb.sub_prev_self_st(TpToken::default(), Vec::new()).unwrap();

    assert_eq!(user[0], ydb[0]);
}
