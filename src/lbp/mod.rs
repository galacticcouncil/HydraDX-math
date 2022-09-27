#![allow(clippy::module_inception)]

mod lbp;

pub use lbp::*;

#[cfg(test)]
mod tests;
mod test_accuracy;
