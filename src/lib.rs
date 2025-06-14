//! A qubit implementation using Clifford algebra.

pub mod error;
pub mod gates;
pub mod qubit;

// Re-export the Qubit type and error types for convenience
pub use error::QubitError;
pub use qubit::Qubit;
