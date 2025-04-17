//! Implementation of Pauli gates for qubits

use crate::qubit::Qubit;
use clifford_3_even::{Ix, Iy, Iz};

/// Applies the Pauli X gate to a qubit.
///
/// The Pauli X gate flips the state of a qubit's complex coefficients:
/// X|0⟩ = |1⟩ and X|1⟩ = |0⟩, or more generally,
/// X|(α β)⟩ = |(β α)⟩
///
/// Mathematically, this is implemented as Ix.reverse() * q * Iz
/// where q is the input qubit's rotor, which results in the same
/// switching of the coefficients when using the standard mapping of
/// the rotor to the complex coefficients:
///
///  -Ix(a_0 + a_zIz + -Iy(a_y + a_xIz))Iz = a_y + a_xIz + -Iy(a_0 + a_zIz)
///
/// but more generally is transforming:
/// a_0 from a scalar to a bivector component of equal magnitude in the -Iy
/// plane, a_y from a bivector in the Iy plane to a scalar. So the scalar and Iy
/// components are swapped and negated. while,
/// a_x from a bivector in the Ix plane to a bivector in the Iz plane,
/// a_z from a bivector in the Iz plane to a bivector in the Ix plane. So the Ix
/// and Iz components are swapped.
///
/// # Arguments
///
/// * `qubit` - The input qubit
///
/// # Returns
///
/// The same qubit with the X gate applied
#[must_use]
pub fn x(qubit: &mut Qubit) -> &mut Qubit {
    qubit.rotor = Ix.reverse() * qubit.rotor * Iz;
    qubit
}

/// Applies the Pauli Y gate to a qubit.
///
/// The Pauli Y gate, similar to the X gate, flips the state of a qubit and
/// introduces a phase shift:
/// Y|0⟩ = i|1⟩ and Y|1⟩ = -i|0⟩, or more generally,
/// Y|(α β)⟩ = |(-iβ iα)⟩
///
/// Mathematically, this is implemented as Iy.reverse() * q * Iz
/// where q is the input qubit's rotor which results in the same
/// transformation of the coefficients.
///
///  -Iy(a_0 + a_zIz -Iy(a_y + a_xIz))Iz = a_x - a_yIz -Iy(-a_z + a_0Iz)
///
/// # Arguments
///
/// * `qubit` - The input qubit
///
/// # Returns
///
/// The same qubit with the Y gate applied
#[must_use]
pub fn y(qubit: &mut Qubit) -> &mut Qubit {
    // Apply the Y gate: Iy.reverse() * q * Iz directly to the qubit's rotor
    qubit.rotor = Iy.reverse() * qubit.rotor * Iz;

    // Return the modified qubit
    qubit
}

/// Applies the Pauli Z gate to a qubit.
///
/// The Pauli Z gate is a rotation around the Z-axis:
/// Z|0⟩ = |0⟩ and Z|1⟩ = -|1⟩
///
/// Mathematically, this is implemented as Iz.reverse() * q * Iz
/// where q is the input qubit's rotor.
///
/// # Arguments
///
/// * `qubit` - The input qubit
///
/// # Returns
///
/// The same qubit with the Z gate applied
#[must_use]
pub fn z(qubit: &mut Qubit) -> &mut Qubit {
    // Apply the Z gate: Iz.reverse() * q * Iz directly to the qubit's rotor
    qubit.rotor = Iz.reverse() * qubit.rotor * Iz;

    // Return the modified qubit
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
    #[case::zero_i_to_one_i(
        Complex64::new(0.0, 1.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(0.0, 1.0)
    )] // i|0⟩ → i|1⟩
    #[case::one_i_to_zero_i(
        Complex64::new(0.0, 0.0),
        Complex64::new(0.0, 1.0),
        Complex64::new(0.0, 1.0),
        Complex64::new(0.0, 0.0)
    )] // i|1⟩ → i|0⟩
    #[case::plus_to_plus(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0)
    )] // |+⟩ → |+⟩
    #[case::minus_to_negative_minus(
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
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(0.0, 1.0)
    )] // |0⟩ → i|1⟩
    #[case::one_to_minus_i_zero(
        Complex64::new(0.0, 0.0),
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, -1.0),
        Complex64::new(0.0, 0.0)
    )] // |1⟩ → -i|0⟩
    #[case::i_zero_to_minus_one(
        Complex64::new(0.0, 1.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(-1.0, 0.0)
    )] // i|0⟩ → -|1⟩
    #[case::i_one_to_zero(
        Complex64::new(0.0, 0.0),
        Complex64::new(0.0, 1.0),
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0)
    )] // i|1⟩ → |0⟩
    #[case::plus_to_i_minus(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(0.0, -FRAC_1_SQRT_2),
        Complex64::new(0.0, FRAC_1_SQRT_2)
    )] // |+⟩ → i|-⟩
    #[case::minus_to_i_plus(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(-FRAC_1_SQRT_2, 0.0),
        Complex64::new(0.0, FRAC_1_SQRT_2),
        Complex64::new(0.0, FRAC_1_SQRT_2)
    )] // |-⟩ → i|+⟩
    fn test_y_gate(
        #[case] alpha_in: Complex64,
        #[case] beta_in: Complex64,
        #[case] alpha_out: Complex64,
        #[case] beta_out: Complex64,
    ) {
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
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0)
    )] // |0⟩ → |0⟩
    #[case::one_to_minus_one(
        Complex64::new(0.0, 0.0),
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(-1.0, 0.0)
    )] // |1⟩ → -|1⟩
    #[case::plus_to_minus(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(-FRAC_1_SQRT_2, 0.0)
    )] // |+⟩ → |-⟩
    #[case::minus_to_plus(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(-FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0)
    )] // |-⟩ → |+⟩
    fn test_z_gate(
        #[case] alpha_in: Complex64,
        #[case] beta_in: Complex64,
        #[case] alpha_out: Complex64,
        #[case] beta_out: Complex64,
    ) {
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
