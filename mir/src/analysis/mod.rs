#[cfg_attr(
    not(test),
    deprecated(note = "Replaced by NLL; use mir::analysis::nll::NllChecker")
)]
pub mod borrow;
pub mod liveness;
pub mod nll;
pub mod ownership;
pub mod typing;

#[cfg(test)]
mod nll_tests;
