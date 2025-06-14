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
            QubitError::NotNormalized { norm_squared } => {
                write!(
                    f,
                    "Qubit coefficients are not normalized: |α|² + |β|² = {} (expected 1.0)",
                    norm_squared
                )
            }
        }
    }
}

impl std::error::Error for QubitError {}
