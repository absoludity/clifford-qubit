//! Implementation of rotation gates for qubits using the Clifford 3 Even library
//!
//! This module provides the three fundamental rotation gates (RX, RY, RZ) that
//! rotate qubits around the respective axes of the Bloch sphere by a given angle theta.
//!
//! The explanations and tests here use the non-rotor complex coordinates so
//! that we can verify it's the same as the matrix operations. I'd like to add
//! separate tests demonstrating what's actually happening with a rotor too.

use clifford_3_even::Rotor;

use crate::qubit::Qubit;

/// Applies the RX gate to a qubit.
///
/// The RX gate performs a rotation around the X-axis of the Bloch sphere by angle theta:
/// RX(θ) = cos(θ/2)I - i*sin(θ/2)X
///
/// This is equivalent to the matrix:
/// ```text
/// RX(θ) = [ cos(θ/2)  -i*sin(θ/2) ]
///         [-i*sin(θ/2)  cos(θ/2)  ]
/// ```
///
/// # Arguments
///
/// * `qubit` - The input qubit
/// * `theta` - The rotation angle in radians
///
/// # Returns
///
/// The same qubit with the RX gate applied
#[must_use]
pub fn rx(qubit: &mut Qubit, theta: f64) -> &mut Qubit {
    qubit.rotor = Rotor::from_axis_angle([1.0, 0.0, 0.0], -theta / 2.0) * qubit.rotor;
    qubit
}

/// Applies the RY gate to a qubit.
///
/// The RY gate performs a rotation around the Y-axis by angle theta:
/// RY(θ) = cos(θ/2)I - i*sin(θ/2)Y
///
/// This is equivalent to the matrix:
/// ```text
/// RY(θ) = [ cos(θ/2)  -sin(θ/2) ]
///         [ sin(θ/2)   cos(θ/2) ]
/// ```
///
/// # Arguments
///
/// * `qubit` - The input qubit
/// * `theta` - The rotation angle in radians
///
/// # Returns
///
/// The same qubit with the RY gate applied
#[must_use]
pub fn ry(qubit: &mut Qubit, theta: f64) -> &mut Qubit {
    qubit.rotor = Rotor::from_axis_angle([0.0, 1.0, 0.0], -theta / 2.0) * qubit.rotor;
    qubit
}

/// Applies the RZ gate to a qubit.
///
/// The RZ gate performs a rotation around the Z-axis by angle theta:
/// RZ(θ) = cos(θ/2)I - i*sin(θ/2)Z
///
/// This is equivalent to the matrix:
/// ```text
/// RZ(θ) = [ e^(-iθ/2)      0      ]
///         [     0      e^(iθ/2)  ]
/// ```
///
/// # Arguments
///
/// * `qubit` - The input qubit
/// * `theta` - The rotation angle in radians
///
/// # Returns
///
/// The same qubit with the RZ gate applied
#[must_use]
pub fn rz(qubit: &mut Qubit, theta: f64) -> &mut Qubit {
    qubit.rotor = Rotor::from_axis_angle([0.0, 0.0, 1.0], -theta / 2.0) * qubit.rotor;
    qubit
}

#[cfg(test)]
mod tests {
    use super::*;
    use num::complex::Complex64;
    use num::complex::ComplexFloat;
    use rstest::rstest;
    use std::f64::consts::{FRAC_1_SQRT_2, FRAC_PI_2, PI};

    #[rstest]
    #[case::zero_pi_rotation(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        PI,
        (Complex64::new(0.0, 0.0), Complex64::new(0.0, -1.0))
    )] // |0⟩ → -i|1⟩ (π rotation)
    #[case::one_pi_rotation(
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0)),
        PI,
        (Complex64::new(0.0, -1.0), Complex64::new(0.0, 0.0))
    )] // |1⟩ → -i|0⟩ (π rotation)
    #[case::zero_pi_half_rotation(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        FRAC_PI_2,
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(0.0, -FRAC_1_SQRT_2))
    )] // |0⟩ → (1/√2)|0⟩ - (i/√2)|1⟩ (π/2 rotation)
    #[case::one_pi_half_rotation(
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0)),
        FRAC_PI_2,
        (Complex64::new(0.0, -FRAC_1_SQRT_2), Complex64::new(FRAC_1_SQRT_2, 0.0))
    )] // |1⟩ → -(i/√2)|0⟩ + (1/√2)|1⟩ (π/2 rotation)
    #[case::zero_no_rotation(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        0.0,
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0))
    )] // |0⟩ → |0⟩ (no rotation)
    #[case::plus_pi_rotation(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0)),
        PI,
        (Complex64::new(0.0, -FRAC_1_SQRT_2), Complex64::new(0.0, -FRAC_1_SQRT_2))
    )] // |+⟩ → -i|+⟩ (π rotation around X)
    fn test_rx_gate(
        #[case] input_coeffs: (Complex64, Complex64),
        #[case] theta: f64,
        #[case] expected_coeffs: (Complex64, Complex64),
    ) {
        let (alpha_in, beta_in) = input_coeffs;
        let (alpha_out, beta_out) = expected_coeffs;

        let mut qubit = Qubit::new(alpha_in, beta_in).unwrap();
        let _ = rx(&mut qubit, theta);

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
    #[case::zero_pi_rotation(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        PI,
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0))
    )] // |0⟩ → |1⟩ (π rotation)
    #[case::one_pi_rotation(
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0)),
        PI,
        (Complex64::new(-1.0, 0.0), Complex64::new(0.0, 0.0))
    )] // |1⟩ → -|0⟩ (π rotation)
    #[case::zero_pi_half_rotation(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        FRAC_PI_2,
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0))
    )] // |0⟩ → (1/√2)|0⟩ + (1/√2)|1⟩ (π/2 rotation)
    #[case::one_pi_half_rotation(
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0)),
        FRAC_PI_2,
        (Complex64::new(-FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0))
    )] // |1⟩ → -(1/√2)|0⟩ + (1/√2)|1⟩ (π/2 rotation)
    #[case::zero_no_rotation(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        0.0,
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0))
    )] // |0⟩ → |0⟩ (no rotation)
    #[case::plus_pi_rotation(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0)),
        PI,
        (Complex64::new(-FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0))
    )] // |+⟩ → |-⟩ (π rotation around Y)
    fn test_ry_gate(
        #[case] input_coeffs: (Complex64, Complex64),
        #[case] theta: f64,
        #[case] expected_coeffs: (Complex64, Complex64),
    ) {
        let (alpha_in, beta_in) = input_coeffs;
        let (alpha_out, beta_out) = expected_coeffs;

        let mut qubit = Qubit::new(alpha_in, beta_in).unwrap();
        let _ = ry(&mut qubit, theta);

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
    #[case::zero_pi_rotation(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        PI,
        (Complex64::new(0.0, -1.0), Complex64::new(0.0, 0.0))
    )] // |0⟩ → -i|0⟩ (π rotation)
    #[case::one_pi_rotation(
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0)),
        PI,
        (Complex64::new(0.0, 0.0), Complex64::new(0.0, 1.0))
    )] // |1⟩ → i|1⟩ (π rotation)
    #[case::zero_pi_half_rotation(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        FRAC_PI_2,
        (Complex64::new(FRAC_1_SQRT_2, -FRAC_1_SQRT_2), Complex64::new(0.0, 0.0))
    )] // |0⟩ → (1-i)/√2|0⟩ (π/2 rotation)
    #[case::one_pi_half_rotation(
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0)),
        FRAC_PI_2,
        (Complex64::new(0.0, 0.0), Complex64::new(FRAC_1_SQRT_2, FRAC_1_SQRT_2))
    )] // |1⟩ → (1+i)/√2|1⟩ (π/2 rotation)
    #[case::zero_no_rotation(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        0.0,
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0))
    )] // |0⟩ → |0⟩ (no rotation)
    #[case::plus_pi_rotation(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0)),
        PI,
        (Complex64::new(0.0, -FRAC_1_SQRT_2), Complex64::new(0.0, FRAC_1_SQRT_2))
    )] // |+⟩ → (-i|0⟩ + i|1⟩)/√2 (π rotation around Z)
    fn test_rz_gate(
        #[case] input_coeffs: (Complex64, Complex64),
        #[case] theta: f64,
        #[case] expected_coeffs: (Complex64, Complex64),
    ) {
        let (alpha_in, beta_in) = input_coeffs;
        let (alpha_out, beta_out) = expected_coeffs;

        let mut qubit = Qubit::new(alpha_in, beta_in).unwrap();
        let _ = rz(&mut qubit, theta);

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
}
