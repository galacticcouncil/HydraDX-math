mod math;
// mod rational;

#[cfg(test)]
pub(crate) mod high_precision;
#[cfg(test)]
mod invariants;
#[cfg(test)]
mod tests;

pub use math::*;
