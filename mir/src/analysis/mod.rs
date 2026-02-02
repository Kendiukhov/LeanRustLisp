pub mod ownership;
#[deprecated(note = "Replaced by NLL; use mir::analysis::nll::NllChecker")]
pub mod borrow;
pub mod liveness;
pub mod nll;

#[cfg(test)]
mod nll_tests;
