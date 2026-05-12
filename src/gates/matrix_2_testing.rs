//! Testing utilities for 2-qubit quantum gates using matrix operations
//!
//! This module provides 2-qubit quantum gate matrices for validating quantum gate
//! implementations against authoritative matrix representations.

use num::complex::Complex64;

/// 4x4 complex matrix for 2-qubit operations
pub struct TwoQubitMatrix {
    pub data: [[Complex64; 4]; 4],
}

impl TwoQubitMatrix {
    pub fn new(data: [[Complex64; 4]; 4]) -> Self {
        Self { data }
    }

    /// Apply matrix to 2-qubit state (|00⟩, |01⟩, |10⟩, |11⟩)
    pub fn apply(
        &self,
        state: (Complex64, Complex64, Complex64, Complex64),
    ) -> (Complex64, Complex64, Complex64, Complex64) {
        let (a00, a01, a10, a11) = state;
        let input = [a00, a01, a10, a11];
        let mut output = [Complex64::new(0.0, 0.0); 4];

        for i in 0..4 {
            for j in 0..4 {
                output[i] += self.data[i][j] * input[j];
            }
        }

        (output[0], output[1], output[2], output[3])
    }
}

/// Returns a matrix representing the CNOT (CX) gate
/// Control qubit is the first qubit, target qubit is the second qubit
/// Basis ordering: |00⟩, |01⟩, |10⟩, |11⟩
pub fn cx() -> TwoQubitMatrix {
    TwoQubitMatrix::new([
        // |00⟩ -> |00⟩
        [
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |01⟩ -> |01⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |10⟩ -> |11⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
        ],
        // |11⟩ -> |10⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
    ])
}

/// Returns a matrix representing the CZ gate
/// Control qubit is the first qubit, target qubit is the second qubit
/// Basis ordering: |00⟩, |01⟩, |10⟩, |11⟩
pub fn cz() -> TwoQubitMatrix {
    TwoQubitMatrix::new([
        // |00⟩ -> |00⟩
        [
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |01⟩ -> |01⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |10⟩ -> |10⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |11⟩ -> -|11⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(-1.0, 0.0),
        ],
    ])
}

/// Returns a matrix representing the SWAP gate
/// Swaps the two qubits
/// Basis ordering: |00⟩, |01⟩, |10⟩, |11⟩
pub fn swap() -> TwoQubitMatrix {
    TwoQubitMatrix::new([
        // |00⟩ -> |00⟩
        [
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |01⟩ -> |10⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |10⟩ -> |01⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |11⟩ -> |11⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
        ],
    ])
}

/// Helper function to verify 2-qubit quantum gate implementations against matrix operations.
///
/// This function allows testing that the expected output for a test is what matrix
/// operations would also generate.
///
/// # Arguments
///
/// * `input_coeffs` - The initial 2-qubit state as (|00⟩, |01⟩, |10⟩, |11⟩) coefficients
/// * `expected_coeffs` - The expected final state as (|00⟩, |01⟩, |10⟩, |11⟩) coefficients
/// * `matrix_op` - A closure that applies matrix operations
///
/// # Panics
///
/// This function will panic if the matrix results don't match the expected
/// coefficients within a tolerance of 1e-10.
pub fn assert_matrix_result<F>(
    input_coeffs: (Complex64, Complex64, Complex64, Complex64),
    expected_coeffs: (Complex64, Complex64, Complex64, Complex64),
    matrix_op: F,
) where
    F: FnOnce() -> TwoQubitMatrix,
{
    // Get the matrix representation of the gate
    let gate_matrix = matrix_op();

    // Apply the matrix to the input state
    let result = gate_matrix.apply(input_coeffs);

    // Check that the result matches the expected output
    let tolerance = 1e-10;
    assert!(
        (result.0 - expected_coeffs.0).norm() < tolerance,
        "|00⟩ coefficient mismatch: expected {}, got {}, error={}",
        expected_coeffs.0,
        result.0,
        (result.0 - expected_coeffs.0).norm()
    );
    assert!(
        (result.1 - expected_coeffs.1).norm() < tolerance,
        "|01⟩ coefficient mismatch: expected {}, got {}, error={}",
        expected_coeffs.1,
        result.1,
        (result.1 - expected_coeffs.1).norm()
    );
    assert!(
        (result.2 - expected_coeffs.2).norm() < tolerance,
        "|10⟩ coefficient mismatch: expected {}, got {}, error={}",
        expected_coeffs.2,
        result.2,
        (result.2 - expected_coeffs.2).norm()
    );
    assert!(
        (result.3 - expected_coeffs.3).norm() < tolerance,
        "|11⟩ coefficient mismatch: expected {}, got {}, error={}",
        expected_coeffs.3,
        result.3,
        (result.3 - expected_coeffs.3).norm()
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cx_gate() {
        // Test |00⟩ -> |00⟩
        let input = (
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        let expected = (
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        assert_matrix_result(input, expected, cx);

        // Test |01⟩ -> |01⟩
        let input = (
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        let expected = (
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        assert_matrix_result(input, expected, cx);

        // Test |10⟩ -> |11⟩
        let input = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        let expected = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
        );
        assert_matrix_result(input, expected, cx);

        // Test |11⟩ -> |10⟩
        let input = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
        );
        let expected = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        assert_matrix_result(input, expected, cx);
    }
}
