//! Implementation of Pauli gates for qubits

use crate::Qubit;
use clifford_3_even::{Ix, Iz};

/// Applies the Pauli X gate to a qubit.
///
/// The Pauli X gate flips the state of a qubit:
/// X|0⟩ = |1⟩ and X|1⟩ = |0⟩
///
/// Mathematically, this is implemented as Ix.reverse() * q * Iz
/// where q is the input qubit's rotor.
///
/// # Arguments
///
/// * `qubit` - The input qubit
///
/// # Returns
///
/// A new qubit with the X gate applied
#[must_use]
pub fn x(qubit: &Qubit) -> Qubit {
    // Get the rotor representation of the qubit
    let q_rotor = qubit.rotor();

    // Apply the X gate: Ix.reverse() * q * Iz
    let result_rotor = Ix.reverse() * q_rotor * Iz;

    // Create a new qubit with the resulting rotor
    Qubit::from_rotor(result_rotor)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num::complex::Complex64;
    use num::complex::ComplexFloat;
    use rstest::rstest;
    use std::f64::consts::FRAC_1_SQRT_2;

    #[rstest]
    #[case::zero_to_one(
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(1.0, 0.0)
    )] // |0⟩ → |1⟩
    #[case::one_to_zero(
        Complex64::new(0.0, 0.0),
        Complex64::new(1.0, 0.0),
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0)
    )] // |1⟩ → |0⟩
    #[case::plus_to_plus(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0)
    )] // |+⟩ → |+⟩
    #[case::minus_to_minus(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(-FRAC_1_SQRT_2, 0.0),
        Complex64::new(-FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0)
    )] // |-⟩ → -|-⟩
    fn test_x_gate(
        #[case] alpha_in: Complex64,
        #[case] beta_in: Complex64,
        #[case] alpha_out: Complex64,
        #[case] beta_out: Complex64,
    ) {
        let qubit = Qubit::new(alpha_in, beta_in).unwrap();
        let result = x(&qubit);

        let (result_alpha, result_beta) = result.complex_coefficients();

        assert!((result_alpha - alpha_out).abs() < 1e-10);
        assert!((result_beta - beta_out).abs() < 1e-10);

        // Create the expected output qubit
        let expected = Qubit::new(alpha_out, beta_out).unwrap();
        assert!(result.approx_eq(&expected, 1e-10));
    }
}
