//! A qubit implementation using Clifford algebra.

pub mod gates;
pub mod qubit;
pub mod simulator;
pub mod matrix_testing;

// Re-export the Qubit type for convenience
pub use qubit::Qubit;
