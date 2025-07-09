//! Single-qubit gate implementations

pub mod hadamard;
pub mod pauli;
pub mod phase;
pub mod rotation;

// Re-export all single gate functions for convenience
pub use hadamard::hadamard;
pub use pauli::{x, y, z};
pub use phase::{s, t};
pub use rotation::{rx, ry, rz};
