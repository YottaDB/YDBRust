 #[macro_use] extern crate yottadb;

use std::fs::File;
use std::io::prelude::*;
use std::error::Error;

use yottadb::simple_api::{DeleteType};
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
    let words = words.split(" ");
    let mut word_key = make_ckey!(ctx, "^words", "");
    for word in words {
        let word = word.to_lowercase();
        if word != "" {
            word_key[1] = Vec::from(word);
            word_key.increment(None)?;
        }
    }
    // Iterate through all words and put them into a global ordered by frequency
    word_key[1] = Vec::from("");
    for k in word_key.clone().iter_subs_values() {
        let (k, v) = k?;
        let v = String::from_utf8_lossy(&v);
        let word = k;
        let mut key = make_ckey!(ctx, "^index", v.into_owned(), word);
        key.set(&Vec::from(""))?;
    }

    // Iterate through the index and output things
    let mut freq_key = make_ckey!(ctx, "^index", "");
    let mut word_key = make_ckey!(ctx, "^index", "", "");
    for k in freq_key.iter_subs_reverse() {
        let v = k?;
        word_key[1] = v;
        word_key[2] = Vec::from("");
        for k2 in word_key.iter_key_subs() {
            let k2 = k2?;
            let v2 = String::from_utf8_lossy(&k2[2]);
            let v1 = String::from_utf8_lossy(&k2[1]);
            println!("{}\t{}", v1, v2);
        }
    }
    Ok(())
}
