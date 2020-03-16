//! Find the frequency of words in a file
//! Expects the file to be named `wordfreq_input.txt` in the current directory.

#[macro_use]
extern crate yottadb;

use std::fs::File;
use std::io::prelude::*;
use std::error::Error;

use yottadb::DeleteType;
use yottadb::context_api::Context;

fn main() -> Result<(), Box<dyn Error>> {
    // Clean out old values
    let ctx = Context::new();
    let mut del_key = make_ckey!(ctx, "^words");
    del_key.delete(DeleteType::DelTree)?;
    del_key = make_ckey!(ctx, "^index");
    del_key.delete(DeleteType::DelTree)?;
    let mut infile = File::open("wordfreq_input.txt")?;
    let mut contents = String::new();
    infile.read_to_string(&mut contents)?;
    let words = contents.replace("\n", " ");
    let words = words.split(' ');
    let mut word_key = make_ckey!(ctx, "^words", "");
    for word in words {
        let word = word.to_lowercase();
        if word != "" {
            word_key[0] = Vec::from(word);
            word_key.increment(None)?;
        }
    }
    // Iterate through all words and put them into a global ordered by frequency
    word_key[0] = Vec::from("");
    for k in word_key.iter_subs_values() {
        let (k, v) = k?;
        let word = k;
        let key = make_ckey!(ctx, "^index", v, word);
        key.set(b"")?;
    }

    // Iterate through the index and output things
    let mut freq_key = make_ckey!(ctx, "^index", "");
    let mut word_key = make_ckey!(ctx, "^index", "", "");
    for k in freq_key.iter_subs_reverse() {
        let v = k?;
        word_key[0] = v;
        word_key[1] = Vec::from("");
        for k2 in word_key.iter_key_subs() {
            let k2 = k2?;
            let v2 = String::from_utf8_lossy(&k2[1]);
            let v1 = String::from_utf8_lossy(&k2[0]);
            println!("{}\t{}", v1, v2);
        }
    }
    Ok(())
}
