//! Testing utilities for 3-qubit quantum gates using matrix operations
//!
//! This module provides 3-qubit quantum gate matrices for validating quantum gate
//! implementations against authoritative matrix representations.

use num::complex::Complex64;

/// 8x8 complex matrix for 3-qubit operations
pub struct ThreeQubitMatrix {
    pub data: [[Complex64; 8]; 8],
}

impl ThreeQubitMatrix {
    pub fn new(data: [[Complex64; 8]; 8]) -> Self {
        Self { data }
    }

    /// Apply matrix to 3-qubit state (|000⟩, |001⟩, |010⟩, |011⟩, |100⟩, |101⟩, |110⟩, |111⟩)
    pub fn apply(
        &self,
        state: (
            Complex64,
            Complex64,
            Complex64,
            Complex64,
            Complex64,
            Complex64,
            Complex64,
            Complex64,
        ),
    ) -> (
        Complex64,
        Complex64,
        Complex64,
        Complex64,
        Complex64,
        Complex64,
        Complex64,
        Complex64,
    ) {
        let (a000, a001, a010, a011, a100, a101, a110, a111) = state;
        let input = [a000, a001, a010, a011, a100, a101, a110, a111];
        let mut output = [Complex64::new(0.0, 0.0); 8];

        for i in 0..8 {
            for j in 0..8 {
                output[i] += self.data[i][j] * input[j];
            }
        }

        (
            output[0], output[1], output[2], output[3], output[4], output[5], output[6], output[7],
        )
    }
}

/// Returns a matrix representing the CCX (Toffoli) gate
/// Control qubits are the first two qubits, target qubit is the third qubit
/// Basis ordering: |000⟩, |001⟩, |010⟩, |011⟩, |100⟩, |101⟩, |110⟩, |111⟩
pub fn ccx() -> ThreeQubitMatrix {
    ThreeQubitMatrix::new([
        // |000⟩ -> |000⟩
        [
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |001⟩ -> |001⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |010⟩ -> |010⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |011⟩ -> |011⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |100⟩ -> |100⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |101⟩ -> |101⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |110⟩ -> |111⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
        ],
        // |111⟩ -> |110⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
    ])
}

/// Returns a matrix representing the Fredkin (CSWAP) gate
/// Control qubit is the first qubit, target qubits are the second and third qubits
/// Basis ordering: |000⟩, |001⟩, |010⟩, |011⟩, |100⟩, |101⟩, |110⟩, |111⟩
pub fn cswap() -> ThreeQubitMatrix {
    ThreeQubitMatrix::new([
        // |000⟩ -> |000⟩
        [
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |001⟩ -> |001⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |010⟩ -> |010⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |011⟩ -> |011⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |100⟩ -> |100⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |101⟩ -> |110⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |110⟩ -> |101⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        ],
        // |111⟩ -> |111⟩
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
        ],
    ])
}

/// Helper function to verify 3-qubit quantum gate implementations against matrix operations.
///
/// This function allows testing that the expected output for a test is what matrix
/// operations would also generate.
///
/// # Arguments
///
/// * `input_coeffs` - The initial 3-qubit state as (|000⟩, |001⟩, |010⟩, |011⟩, |100⟩, |101⟩, |110⟩, |111⟩) coefficients
/// * `expected_coeffs` - The expected final state as (|000⟩, |001⟩, |010⟩, |011⟩, |100⟩, |101⟩, |110⟩, |111⟩) coefficients
/// * `matrix_op` - A closure that applies matrix operations
///
/// # Panics
///
/// This function will panic if the matrix results don't match the expected
/// coefficients within a tolerance of 1e-10.
pub fn assert_matrix_result<F>(
    input_coeffs: (
        Complex64,
        Complex64,
        Complex64,
        Complex64,
        Complex64,
        Complex64,
        Complex64,
        Complex64,
    ),
    expected_coeffs: (
        Complex64,
        Complex64,
        Complex64,
        Complex64,
        Complex64,
        Complex64,
        Complex64,
        Complex64,
    ),
    matrix_op: F,
) where
    F: FnOnce() -> ThreeQubitMatrix,
{
    // Get the matrix representation of the gate
    let gate_matrix = matrix_op();

    // Apply the matrix to the input state
    let result = gate_matrix.apply(input_coeffs);

    // Check that the result matches the expected output
    let tolerance = 1e-10;
    let basis_states = [
        "|000⟩", "|001⟩", "|010⟩", "|011⟩", "|100⟩", "|101⟩", "|110⟩", "|111⟩",
    ];
    let result_array = [
        result.0, result.1, result.2, result.3, result.4, result.5, result.6, result.7,
    ];
    let expected_array = [
        expected_coeffs.0,
        expected_coeffs.1,
        expected_coeffs.2,
        expected_coeffs.3,
        expected_coeffs.4,
        expected_coeffs.5,
        expected_coeffs.6,
        expected_coeffs.7,
    ];

    for i in 0..8 {
        assert!(
            (result_array[i] - expected_array[i]).norm() < tolerance,
            "{} coefficient mismatch: expected {}, got {}, error={}",
            basis_states[i],
            expected_array[i],
            result_array[i],
            (result_array[i] - expected_array[i]).norm()
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ccx_gate() {
        // Test |000⟩ -> |000⟩ (both controls are 0)
        let input = (
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        let expected = input;
        assert_matrix_result(input, expected, ccx);

        // Test |001⟩ -> |001⟩ (both controls are 0)
        let input = (
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        let expected = input;
        assert_matrix_result(input, expected, ccx);

        // Test |010⟩ -> |010⟩ (first control is 0)
        let input = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        let expected = input;
        assert_matrix_result(input, expected, ccx);

        // Test |100⟩ -> |100⟩ (second control is 0)
        let input = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        let expected = input;
        assert_matrix_result(input, expected, ccx);

        // Test |110⟩ -> |111⟩ (both controls are 1, target flipped)
        let input = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        let expected = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
        );
        assert_matrix_result(input, expected, ccx);

        // Test |111⟩ -> |110⟩ (both controls are 1, target flipped)
        let input = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
        );
        let expected = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        assert_matrix_result(input, expected, ccx);
    }

    #[test]
    fn test_cswap_gate() {
        // Test |000⟩ -> |000⟩ (control is 0)
        let input = (
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        let expected = input;
        assert_matrix_result(input, expected, cswap);

        // Test |101⟩ -> |110⟩ (control is 1, targets swapped)
        let input = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        let expected = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        assert_matrix_result(input, expected, cswap);

        // Test |110⟩ -> |101⟩ (control is 1, targets swapped)
        let input = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        let expected = (
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(1.0, 0.0),
            Complex64::new(0.0, 0.0),
            Complex64::new(0.0, 0.0),
        );
        assert_matrix_result(input, expected, cswap);
    }
}
