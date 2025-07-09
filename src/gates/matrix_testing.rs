//! Testing utilities for quantum gates using matrix operations
//!
//! This module provides quantum gate matrices extracted from QIR matrix_testing module
//! for validating quantum gate implementations against authoritative matrix representations.

use num::complex::Complex64;
use std::f64::consts::FRAC_1_SQRT_2;

/// 2x2 complex matrix for single-qubit operations
pub struct QubitMatrix {
    pub data: [[Complex64; 2]; 2],
}

impl QubitMatrix {
    pub fn new(data: [[Complex64; 2]; 2]) -> Self {
        Self { data }
    }

    /// Apply matrix to qubit state (alpha, beta)
    pub fn apply(&self, state: (Complex64, Complex64)) -> (Complex64, Complex64) {
        let (alpha, beta) = state;
        let new_alpha = self.data[0][0] * alpha + self.data[0][1] * beta;
        let new_beta = self.data[1][0] * alpha + self.data[1][1] * beta;
        (new_alpha, new_beta)
    }
}

/// Returns a matrix representing the `X` (Pauli-X) gate
pub fn x() -> QubitMatrix {
    QubitMatrix::new([
        [Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0)],
        [Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)],
    ])
}

/// Returns a matrix representing the `Y` (Pauli-Y) gate
pub fn y() -> QubitMatrix {
    QubitMatrix::new([
        [Complex64::new(0.0, 0.0), Complex64::new(0.0, -1.0)],
        [Complex64::new(0.0, 1.0), Complex64::new(0.0, 0.0)],
    ])
}

/// Returns a matrix representing the `Z` (Pauli-Z) gate
pub fn z() -> QubitMatrix {
    QubitMatrix::new([
        [Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)],
        [Complex64::new(0.0, 0.0), Complex64::new(-1.0, 0.0)],
    ])
}

/// Returns a matrix representing the Hadamard gate
pub fn h() -> QubitMatrix {
    QubitMatrix::new([
        [
            Complex64::new(FRAC_1_SQRT_2, 0.0),
            Complex64::new(FRAC_1_SQRT_2, 0.0),
        ],
        [
            Complex64::new(FRAC_1_SQRT_2, 0.0),
            Complex64::new(-FRAC_1_SQRT_2, 0.0),
        ],
    ])
}

/// Returns a matrix representing the `S` gate
pub fn s() -> QubitMatrix {
    QubitMatrix::new([
        [Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)],
        [Complex64::new(0.0, 0.0), Complex64::new(0.0, 1.0)],
    ])
}

/// Returns a matrix representing the `T` gate
pub fn t() -> QubitMatrix {
    QubitMatrix::new([
        [Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)],
        [
            Complex64::new(0.0, 0.0),
            Complex64::new(FRAC_1_SQRT_2, FRAC_1_SQRT_2),
        ],
    ])
}

/// Returns a matrix representing the `RX` rotation gate
pub fn rx(theta: f64) -> QubitMatrix {
    let cos_theta = f64::cos(theta / 2.0);
    let sin_theta = f64::sin(theta / 2.0);
    QubitMatrix::new([
        [
            Complex64::new(cos_theta, 0.0),
            Complex64::new(0.0, -sin_theta),
        ],
        [
            Complex64::new(0.0, -sin_theta),
            Complex64::new(cos_theta, 0.0),
        ],
    ])
}

/// Helper function to verify quantum gate implementations against matrix operations.
///
/// This function allows testing that the expected output for a test is what matrix
/// operations would also generate.
///
/// # Arguments
///
/// * `input_coeffs` - The initial qubit state as (alpha, beta) coefficients
/// * `expected_coeffs` - The expected final state as (alpha, beta) coefficients
/// * `matrix_op` - A closure that applies matrix operations
///
/// # Panics
///
/// This function will panic if the matrix results don't match the expected
/// coefficients within a tolerance of 1e-10.
pub fn assert_matrix_result<F>(
    input_coeffs: (Complex64, Complex64),
    expected_coeffs: (Complex64, Complex64),
    matrix_op: F,
) where
    F: FnOnce() -> QubitMatrix,
{
    // Get the matrix representation of the gate
    let gate_matrix = matrix_op();

    // Apply the matrix to the input state
    let result = gate_matrix.apply(input_coeffs);

    // Check that the result matches the expected output
    let tolerance = 1e-10;
    assert!(
        (result.0 - expected_coeffs.0).norm() < tolerance,
        "Alpha mismatch: expected {}, got {}, error={}",
        expected_coeffs.0,
        result.0,
        (result.0 - expected_coeffs.0).norm()
    );
    assert!(
        (result.1 - expected_coeffs.1).norm() < tolerance,
        "Beta mismatch: expected {}, got {}, error={}",
        expected_coeffs.1,
        result.1,
        (result.1 - expected_coeffs.1).norm()
    );
}

/// Returns a matrix representing the `RY` rotation gate
pub fn ry(theta: f64) -> QubitMatrix {
    let cos_theta = f64::cos(theta / 2.0);
    let sin_theta = f64::sin(theta / 2.0);
    QubitMatrix::new([
        [
            Complex64::new(cos_theta, 0.0),
            Complex64::new(-sin_theta, 0.0),
        ],
        [
            Complex64::new(sin_theta, 0.0),
            Complex64::new(cos_theta, 0.0),
        ],
    ])
}

/// Returns a matrix representing the `RZ` rotation gate
pub fn rz(theta: f64) -> QubitMatrix {
    let exp_theta = Complex64::exp(Complex64::new(0.0, theta / 2.0));
    let neg_exp_theta = Complex64::exp(Complex64::new(0.0, -theta / 2.0));
    QubitMatrix::new([
        [neg_exp_theta, Complex64::new(0.0, 0.0)],
        [Complex64::new(0.0, 0.0), exp_theta],
    ])
}
