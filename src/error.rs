//! Error types for qubit operations.

use std::fmt;

/// Error type for qubit operations.
#[derive(Debug, Clone, PartialEq)]
pub enum QubitError {
    /// The coefficients are not normalized (|α|² + |β|² ≠ 1)
    NotNormalized { norm_squared: f64 },
}

impl fmt::Display for QubitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotNormalized { norm_squared } => {
                write!(
                    f,
                    "Qubit coefficients are not normalized: |α|² + |β|² = {norm_squared} (expected 1.0)"
                )
            }
        }
    }
}

impl std::error::Error for QubitError {}
