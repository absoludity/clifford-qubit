//! Phase gate implementations for single qubits
//!
//! This module provides implementations for the S and T phase gates.

use std::f64::consts::{FRAC_PI_4, FRAC_PI_8};

use clifford_3_even::Rotor;

use crate::qubit::Qubit;

/// Apply the S gate (phase gate) to a qubit
///
/// The S gate applies a phase shift of π/2 to the |1⟩ state:
/// S|0⟩ = |0⟩
/// S|1⟩ = i|1⟩
///
/// # Arguments
///
/// * `qubit` - The qubit to apply the S gate to
pub fn s(qubit: &mut Qubit) -> &mut Qubit {
    let rotor = Rotor::from_axis_angle([0.0, 0.0, 1.0], FRAC_PI_4);
    qubit.rotor = rotor.reverse() * qubit.rotor * rotor;
    qubit
}

/// Apply the T gate (π/8 gate) to a qubit
///
/// The T gate applies a phase shift of π/4 to the |1⟩ state:
/// T|0⟩ = |0⟩
/// T|1⟩ = e^(iπ/4)|1⟩
///
/// # Arguments
///
/// * `qubit` - The qubit to apply the T gate to
pub fn t(qubit: &mut Qubit) -> &mut Qubit {
    let rotor = Rotor::from_axis_angle([0.0, 0.0, 1.0], FRAC_PI_8);
    qubit.rotor = rotor.reverse() * qubit.rotor * rotor;
    qubit
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gates::matrix_testing::assert_matrix_result;
    use num::complex::Complex64;
    use rstest::rstest;
    use std::f64::consts::FRAC_1_SQRT_2;

    #[rstest]
    #[case::zero_to_zero(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
    )]
    #[case::one_to_i_one(
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0)),
        (Complex64::new(0.0, 0.0), Complex64::new(0.0, 1.0)),
    )]
    #[case::plus_to_plus_i_minus_half(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0)),
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(0.0, FRAC_1_SQRT_2)),
    )]
    #[case::minus_to_minus_i_plus_half(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(-FRAC_1_SQRT_2, 0.0)),
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(0.0, -FRAC_1_SQRT_2)),
    )]
    fn test_s_gate(
        #[case] input_coeffs: (Complex64, Complex64),
        #[case] expected_coeffs: (Complex64, Complex64),
    ) {
        // Verify against matrix operations first to validate expected output
        assert_matrix_result(input_coeffs, expected_coeffs, || {
            crate::gates::matrix_testing::s()
        });

        let (alpha_in, beta_in) = input_coeffs;
        let (alpha_out, beta_out) = expected_coeffs;

        let mut qubit = Qubit::new(alpha_in, beta_in).unwrap();
        let _ = s(&mut qubit);

        let result_coeffs = qubit.complex_coefficients();
        let (result_alpha, result_beta) = result_coeffs;

        // Check that the result matches the expected output
        let tolerance = 1e-10;
        assert!(
            (result_alpha - alpha_out).norm() < tolerance,
            "Alpha mismatch: expected {}, got {}, error={}",
            alpha_out,
            result_alpha,
            (result_alpha - alpha_out).norm()
        );
        assert!(
            (result_beta - beta_out).norm() < tolerance,
            "Beta mismatch: expected {}, got {}, error={}",
            beta_out,
            result_beta,
            (result_beta - beta_out).norm()
        );
    }

    #[rstest]
    #[case::zero_to_zero(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
    )]
    #[case::one_to_exp_i_pi_quarter_one(
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0)),
        (Complex64::new(0.0, 0.0), Complex64::new(FRAC_1_SQRT_2, FRAC_1_SQRT_2)),
    )]
    #[case::plus_to_plus_exp_i_pi_eighth(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0)),
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(0.5, 0.5)),
    )]
    #[case::minus_to_minus_exp_i_pi_eighth(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(-FRAC_1_SQRT_2, 0.0)),
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(-0.5, -0.5)),
    )]
    fn test_t_gate(
        #[case] input_coeffs: (Complex64, Complex64),
        #[case] expected_coeffs: (Complex64, Complex64),
    ) {
        // Verify against matrix operations first to validate expected output
        assert_matrix_result(input_coeffs, expected_coeffs, || {
            crate::gates::matrix_testing::t()
        });

        let (alpha_in, beta_in) = input_coeffs;
        let (alpha_out, beta_out) = expected_coeffs;

        let mut qubit = Qubit::new(alpha_in, beta_in).unwrap();
        let _ = t(&mut qubit);

        let result_coeffs = qubit.complex_coefficients();
        let (result_alpha, result_beta) = result_coeffs;

        // Check that the result matches the expected output
        let tolerance = 1e-10;
        assert!(
            (result_alpha - alpha_out).norm() < tolerance,
            "Alpha mismatch: expected {}, got {}, error={}",
            alpha_out,
            result_alpha,
            (result_alpha - alpha_out).norm()
        );
        assert!(
            (result_beta - beta_out).norm() < tolerance,
            "Beta mismatch: expected {}, got {}, error={}",
            beta_out,
            result_beta,
            (result_beta - beta_out).norm()
        );
    }
}
