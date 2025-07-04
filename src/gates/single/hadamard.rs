//! Implementation of the Hadamard gate for qubits using the Clifford 3 Even library
//!
//! This module provides the Hadamard gate (H) with both reference implementations
//! using rotor multiplication and derived optimized versions using direct coefficient
//! manipulation. The Hadamard gate creates superposition states and is equivalent
//! to the matrix H = (1/√2) * [[1, 1], [1, -1]].

use std::f64::consts::FRAC_1_SQRT_2;

use clifford_3_even::{Iz, Rotor};

use crate::qubit::Qubit;

/// Applies the Hadamard gate to a qubit.
///
/// The Hadamard gate creates superposition states:
/// H|0⟩ = (|0⟩ + |1⟩)/√2 = |+⟩ and H|1⟩ = (|0⟩ - |1⟩)/√2 = |-⟩
///
/// # Arguments
///
/// * `qubit` - The input qubit
///
/// # Returns
///
/// The same qubit with the Hadamard gate applied
#[must_use]
pub fn hadamard(qubit: &mut Qubit) -> &mut Qubit {
    qubit.rotor = Rotor::new(0.0, -FRAC_1_SQRT_2, 0.0, -FRAC_1_SQRT_2) * qubit.rotor * Iz;
    qubit
}

#[cfg(test)]
mod tests {
    use super::*;
    use num::complex::Complex64;
    use num::complex::ComplexFloat;
    use rstest::rstest;
    use std::f64::consts::FRAC_1_SQRT_2;

    #[rstest]
    #[case::zero_to_plus(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0))
    )] // |0⟩ → |+⟩
    #[case::one_to_minus(
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0)),
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(-FRAC_1_SQRT_2, 0.0))
    )] // |1⟩ → |-⟩
    #[case::plus_to_zero(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0)),
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0))
    )] // |+⟩ → |0⟩
    #[case::minus_to_one(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(-FRAC_1_SQRT_2, 0.0)),
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0))
    )] // |-⟩ → |1⟩
    #[case::plus_i_to_plus_i(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(0.0, FRAC_1_SQRT_2)),
        (Complex64::new(0.5, 0.5), Complex64::new(0.5, -0.5))
    )] // |+i⟩ → i|+⟩
    #[case::minus_i_to_minus_i(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(0.0, -FRAC_1_SQRT_2)),
        (Complex64::new(0.5, -0.5), Complex64::new(0.5, 0.5))
    )] // |-i⟩ → -i|+⟩
    fn test_hadamard_gate(
        #[case] input_coeffs: (Complex64, Complex64),
        #[case] expected_coeffs: (Complex64, Complex64),
    ) {
        let (alpha_in, beta_in) = input_coeffs;
        let (alpha_out, beta_out) = expected_coeffs;

        let mut qubit = Qubit::new(alpha_in, beta_in).unwrap();
        let _ = hadamard(&mut qubit);

        let (result_alpha, result_beta) = qubit.complex_coefficients();

        assert!(
            (result_alpha - alpha_out).abs() < 1e-10,
            "Alpha mismatch: expected {}, got {}",
            alpha_out,
            result_alpha
        );
        assert!(
            (result_beta - beta_out).abs() < 1e-10,
            "Beta mismatch: expected {}, got {}",
            beta_out,
            result_beta
        );

        // Create the expected output qubit
        let expected = Qubit::new(alpha_out, beta_out).unwrap();
        assert!(
            qubit.approx_eq(&expected, 1e-10),
            "Qubit mismatch: expected {:?}, got {:?}",
            expected,
            qubit
        );
    }

    #[rstest]
    #[case::zero_state(Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0))] // |0⟩
    #[case::one_state(Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0))] // |1⟩
    #[case::plus_state(Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0))] // |+⟩
    #[case::minus_state(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(-FRAC_1_SQRT_2, 0.0)
    )] // |-⟩
    fn test_hadamard_involution(#[case] alpha: Complex64, #[case] beta: Complex64) {
        // Test that H² = I (Hadamard is its own inverse)
        let original = Qubit::new(alpha, beta).unwrap();
        let mut qubit = original;

        // Apply Hadamard twice
        let _ = hadamard(&mut qubit);
        let _ = hadamard(&mut qubit);

        // Should be back to original state
        assert!(
            qubit.approx_eq(&original, 1e-10),
            "Hadamard involution failed for state ({}, {})",
            alpha,
            beta
        );
    }
}
