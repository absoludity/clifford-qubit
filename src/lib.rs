//! A qubit implementation using Clifford algebra.

pub mod gates;
pub mod qubit;

// Re-export the Qubit type for convenience
pub use qubit::Qubit;
