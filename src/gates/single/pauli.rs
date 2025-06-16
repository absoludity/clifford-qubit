//! Implementation of Pauli gates for qubits using the Clifford 3 Even library
//!
//! This module provides the three fundamental Pauli gates (X, Y, Z) with both
//! reference implementations using rotor multiplication and derived optimized
//! versions using direct coefficient manipulation equivalent to the
//! corresponding Pauli matrices.

use crate::qubit::Qubit;

#[cfg(not(feature = "optimized"))]
use clifford_3_even::{Ix, Iy, Iz};

/// Applies the Pauli X gate to a qubit.
///
/// The Pauli X gate flips the state of a qubit's complex coefficients so that:
/// X|0⟩ = |1⟩ and X|1⟩ = |0⟩, or more generally,
/// X|(α β)⟩ = |(β α)⟩
///
/// Mathematically, this is implemented as `Ix.reverse()` * q * Iz
/// where q is the input qubit's rotor, which results in the same
/// switching of the coefficients when using the chosen mapping of
/// the rotor to the complex coefficients:
///
/// ```text
///  X(q) = -Ix(q)Iz
///       = -Ix(a_0 + a_xIx + a_yIy + a_zIz)Iz
///         which, with q reorganised to show the complex coefficients, is
///         -Ix(a_0 + a_zIz + -Iy(-a_y + a_xIz))Iz
///
///       = -a_y + a_zIx + -a_0Iy + a_xIz
///         which, when reorganised to show the complex coefficients, is
///         -a_y + a_xIz + -Iy(a_0 + a_zIz)
/// ```
/// which is the original qubit with the coefficients swapped. An optimised
/// implementation is provided below that directly manipulates the rotor
/// coefficients.
///
///
/// # Arguments
///
/// * `qubit` - The input qubit
///
/// # Returns
///
/// The same qubit with the X gate applied
#[cfg(not(feature = "optimized"))]
#[must_use]
pub fn x(qubit: &mut Qubit) -> &mut Qubit {
    qubit.rotor = Ix.reverse() * qubit.rotor * Iz;
    qubit
}

/// Optimized implementation of the Pauli X gate using direct coefficient
/// manipulation.
///
/// Based on the worked example above, the X gate performs scalar<->-a_y and
/// a_x<->a_z, matching the Pauli matrix transformation.
///
/// # Arguments
///
/// * `qubit` - The input qubit
///
/// # Returns
///
/// The same qubit with the X gate applied
#[cfg(feature = "optimized")]
#[must_use]
pub fn x(qubit: &mut Qubit) -> &mut Qubit {
    let rotor = &mut qubit.rotor;
    std::mem::swap(&mut rotor.scalar, &mut rotor.iy);
    std::mem::swap(&mut rotor.ix, &mut rotor.iz);
    rotor.scalar = -rotor.scalar;
    rotor.iy = -rotor.iy;
    qubit
}

/// Applies the Pauli Y gate to a qubit.
///
/// The Pauli Y gate, similar to the X gate, flips the state of a qubit and
/// introduces a phase shift:
/// Y|0⟩ = i|1⟩ and Y|1⟩ = -i|0⟩, or more generally,
/// Y|(α β)⟩ = |(-iβ iα)⟩
///
/// Mathematically, this is implemented as `Iy.reverse()` * q * Iz
/// where q is the input qubit's rotor which results in the same
/// transformation of the coefficients:
///
/// ```text
///  Y(q) = -Iy(q)Iz
///       = -Iy(a_0 + a_xIx + a_yIy + a_zIz)Iz
///         which, with q reorganised to show the complex coefficients, is
///         -Iy(a_0 + a_zIz + -Iy(-a_y + a_xIz))Iz
///
///       = a_x + a_0Ix + a_zIy + a_yIz
///         which, when reorganised to show the complex coefficients, is
///         a_x + a_yIz + -Iy(-a_z + a_0Iz)
/// ```
///
/// Which appears like a 0<->1 and a 2<->3 swap of the rotor coefficients.
///
/// # Arguments
///
/// * `qubit` - The input qubit
///
/// # Returns
///
/// The same qubit with the Y gate applied
#[cfg(not(feature = "optimized"))]
#[must_use]
pub fn y(qubit: &mut Qubit) -> &mut Qubit {
    // Apply the Y gate: Iy.reverse() * q * Iz directly to the qubit's rotor
    qubit.rotor = Iy.reverse() * qubit.rotor * Iz;

    // Return the modified qubit
    qubit
}

/// Optimized implementation of the Pauli Y gate using direct coefficient
/// manipulation.
///
/// Based on the worked example above, the Y gate performs a_0<->a_1 and
/// a_2<->a_3 swap of the rotor coefficients, matchig the Pauli matrix
/// transformation.
///
/// # Arguments
///
/// * `qubit` - The input qubit
///
/// # Returns
///
/// The same qubit with the Y gate applied
#[cfg(feature = "optimized")]
#[must_use]
pub fn y(qubit: &mut Qubit) -> &mut Qubit {
    let rotor = &mut qubit.rotor;
    std::mem::swap(&mut rotor.scalar, &mut rotor.ix);
    std::mem::swap(&mut rotor.iy, &mut rotor.iz);
    qubit
}

/// Applies the Pauli Z gate to a qubit.
///
/// The Pauli Z gate is a rotation around the Z-axis:
/// Z|0⟩ = |0⟩ and Z|1⟩ = -|1⟩
///
/// Mathematically, this is implemented as `Iz.reverse()` * q * Iz
/// where q is the input qubit's rotor which results in the same
/// transformation of the coefficients:
///
/// ```text
///  Z(q) = -Iy(q)Iz
///       = -Iz(a_0 + a_xIx + a_yIy + a_zIz)Iz
///         which, with q reorganised to show the complex coefficients, is
///         -Iz(a_0 + a_zIz + -Iy(-a_y + a_xIz))Iz
///
///       = a_0 + -a_xIx + -a_yIy + a_zIz
///         which, when reorganised to show the complex coefficients, is
///         a_0 + a_zIz + -Iy(a_y - a_xIz)
/// ```
///
/// Which appears like a 2->-2 and 3->-3 change of coefficients.
///
/// # Arguments
///
/// * `qubit` - The input qubit
///
/// # Returns
///
/// The same qubit with the Z gate applied
#[cfg(not(feature = "optimized"))]
#[must_use]
pub fn z(qubit: &mut Qubit) -> &mut Qubit {
    // Apply the Z gate: Iz.reverse() * q * Iz directly to the qubit's rotor
    qubit.rotor = Iz.reverse() * qubit.rotor * Iz;

    // Return the modified qubit
    qubit
}

/// Optimized implementation of the Pauli Z gate using direct coefficient
/// manipulation.
///
/// Based on the mathematical analysis, the Z gate negates the a_y and a_x
/// coefficients, matching the Pauli matrix transformation.
///
/// # Arguments
///
/// * `qubit` - The input qubit
///
/// # Returns
///
/// The same qubit with the Z gate applied
#[cfg(feature = "optimized")]
#[must_use]
pub fn z(qubit: &mut Qubit) -> &mut Qubit {
    // Negate coefficients 2 and 3
    let rotor = &mut qubit.rotor;
    rotor.iy = -rotor.iy;
    rotor.ix = -rotor.ix;
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
    #[case::zero_to_one(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0))
    )] // |0⟩ → |1⟩
    #[case::one_to_zero(
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0)),
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0))
    )] // |1⟩ → |0⟩
    #[case::zero_i_to_one_i(
        (Complex64::new(0.0, 1.0), Complex64::new(0.0, 0.0)),
        (Complex64::new(0.0, 0.0), Complex64::new(0.0, 1.0))
    )] // i|0⟩ → i|1⟩
    #[case::one_i_to_zero_i(
        (Complex64::new(0.0, 0.0), Complex64::new(0.0, 1.0)),
        (Complex64::new(0.0, 1.0), Complex64::new(0.0, 0.0))
    )] // i|1⟩ → i|0⟩
    #[case::plus_to_plus(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0)),
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0))
    )] // |+⟩ → |+⟩
    #[case::minus_to_negative_minus(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(-FRAC_1_SQRT_2, 0.0)),
        (Complex64::new(-FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0))
    )] // |-⟩ → -|-⟩
    fn test_x_gate(
        #[case] input_coeffs: (Complex64, Complex64),
        #[case] expected_coeffs: (Complex64, Complex64),
    ) {
        let (alpha_in, beta_in) = input_coeffs;
        let (alpha_out, beta_out) = expected_coeffs;

        let mut qubit = Qubit::new(alpha_in, beta_in).unwrap();
        let _ = x(&mut qubit);

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
        assert!(qubit.approx_eq(&expected, 1e-10));
    }

    #[rstest]
    #[case::zero_to_i_one(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        (Complex64::new(0.0, 0.0), Complex64::new(0.0, 1.0))
    )] // |0⟩ → i|1⟩
    #[case::one_to_minus_i_zero(
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0)),
        (Complex64::new(0.0, -1.0), Complex64::new(0.0, 0.0))
    )] // |1⟩ → -i|0⟩
    #[case::i_zero_to_minus_one(
        (Complex64::new(0.0, 1.0), Complex64::new(0.0, 0.0)),
        (Complex64::new(0.0, 0.0), Complex64::new(-1.0, 0.0))
    )] // i|0⟩ → -|1⟩
    #[case::i_one_to_zero(
        (Complex64::new(0.0, 0.0), Complex64::new(0.0, 1.0)),
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0))
    )] // i|1⟩ → |0⟩
    #[case::plus_to_i_minus(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0)),
        (Complex64::new(0.0, -FRAC_1_SQRT_2), Complex64::new(0.0, FRAC_1_SQRT_2))
    )] // |+⟩ → i|-⟩
    #[case::minus_to_i_plus(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(-FRAC_1_SQRT_2, 0.0)),
        (Complex64::new(0.0, FRAC_1_SQRT_2), Complex64::new(0.0, FRAC_1_SQRT_2))
    )] // |-⟩ → i|+⟩
    fn test_y_gate(
        #[case] input_coeffs: (Complex64, Complex64),
        #[case] expected_coeffs: (Complex64, Complex64),
    ) {
        let (alpha_in, beta_in) = input_coeffs;
        let (alpha_out, beta_out) = expected_coeffs;

        let mut qubit = Qubit::new(alpha_in, beta_in).unwrap();
        println!("initial qubit: {}", qubit.rotor);
        let _ = y(&mut qubit);

        let (result_alpha, result_beta) = qubit.complex_coefficients();

        println!("resulting qubit: {}", qubit.rotor);

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
    #[case::zero_to_zero(
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)),
        (Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0))
    )] // |0⟩ → |0⟩
    #[case::one_to_minus_one(
        (Complex64::new(0.0, 0.0), Complex64::new(1.0, 0.0)),
        (Complex64::new(0.0, 0.0), Complex64::new(-1.0, 0.0))
    )] // |1⟩ → -|1⟩
    #[case::plus_to_minus(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0)),
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(-FRAC_1_SQRT_2, 0.0))
    )] // |+⟩ → |-⟩
    #[case::minus_to_plus(
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(-FRAC_1_SQRT_2, 0.0)),
        (Complex64::new(FRAC_1_SQRT_2, 0.0), Complex64::new(FRAC_1_SQRT_2, 0.0))
    )] // |-⟩ → |+⟩
    fn test_z_gate(
        #[case] input_coeffs: (Complex64, Complex64),
        #[case] expected_coeffs: (Complex64, Complex64),
    ) {
        let (alpha_in, beta_in) = input_coeffs;
        let (alpha_out, beta_out) = expected_coeffs;

        let mut qubit = Qubit::new(alpha_in, beta_in).unwrap();
        let _ = z(&mut qubit);

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
