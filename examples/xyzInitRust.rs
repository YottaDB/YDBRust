#![allow(non_snake_case)]

use yottadb::simple_api::{DeleteType, Key};
use yottadb::context_api::Context;

fn main() {
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
