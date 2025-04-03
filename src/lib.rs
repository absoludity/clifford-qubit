//! A qubit implementation using Clifford algebra.

use clifford_3_even::Rotor;
use num::complex::Complex64;

/// Represents a quantum bit (qubit).
///
/// A qubit is represented by two complex coefficients α and β such that:
/// |ψ⟩ = α|0⟩ + β|1⟩
/// where |α|² + |β|² = 1
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Qubit {
    /// The underlying rotor representation
    rotor: Rotor,
}

impl Qubit {
    /// Creates a new qubit from complex coefficients for |0⟩ and |1⟩ states.
    ///
    /// # Arguments
    ///
    /// * `alpha` - Complex coefficient for the |0⟩ state
    /// * `beta` - Complex coefficient for the |1⟩ state
    ///
    /// # Returns
    ///
    /// Some(Qubit) if the coefficients satisfy |α|² + |β|² = 1, None otherwise
    #[must_use]
    pub fn new(alpha: Complex64, beta: Complex64) -> Option<Self> {
        // Check normalization condition: |α|² + |β|² = 1
        let norm_squared = alpha.norm_sqr() + beta.norm_sqr();
        if (norm_squared - 1.0).abs() > 1e-10 {
            return None;
        }

        // Mapping qubit to the rotor α₀ + α₁Iz + -Iy(β₀ + β₁Iz)
        //                          = α₀ + α₁Iz -β₀Iy + β₁Ix
        //                          = α₀ + β₁Ix -β₀Iy + α₁Iz
        let rotor = Rotor::new(alpha.re, beta.im, -beta.re, alpha.im);

        Some(Self { rotor })
    }

    /// Extracts the complex coefficients of the qubit state.
    ///
    /// # Returns
    ///
    /// A tuple (alpha, beta) of complex coefficients representing the state
    /// |ψ⟩ = α|0⟩ + β|1⟩
    #[must_use]
    pub fn complex_coefficients(&self) -> (Complex64, Complex64) {
        let alpha = Complex64::new(self.rotor.scalar, self.rotor.iz);
        let beta = Complex64::new(-self.rotor.iy, self.rotor.ix);

        (alpha, beta)
    }

    /// Creates a qubit directly from a rotor.
    ///
    /// This is primarily used internally for implementing gates.
    ///
    /// # Arguments
    ///
    /// * `rotor` - The rotor representation of the qubit
    ///
    /// # Returns
    ///
    /// A new qubit with the given rotor
    #[must_use]
    pub fn from_rotor(rotor: Rotor) -> Self {
        Self { rotor }
    }

    /// Returns the rotor representation of the qubit.
    ///
    /// # Returns
    ///
    /// The rotor representing this qubit
    #[must_use]
    pub fn rotor(&self) -> Rotor {
        self.rotor
    }

    /// Checks if this qubit is approximately equal to another qubit.
    ///
    /// This compares the underlying rotor representations.
    ///
    /// # Arguments
    ///
    /// * `other` - The qubit to compare with
    /// * `epsilon` - The maximum allowed difference between components
    ///
    /// # Returns
    ///
    /// `true` if the rotors are approximately equal
    #[must_use]
    pub fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        self.rotor.approx_eq(&other.rotor, epsilon)
    }
}

// Module structure for quantum gates
pub mod gates {
    pub mod single {
        pub mod pauli;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;
    use std::f64::consts::FRAC_1_SQRT_2;

    #[rstest]
    #[case::zero_state(
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0),
        Rotor::new(1.0, 0.0, 0.0, 0.0)
    )] // |0⟩ state
    #[case::one_state(
        Complex64::new(0.0, 0.0),
        Complex64::new(1.0, 0.0),
        Rotor::new(0.0, 0.0, -1.0, 0.0)
    )] // |1⟩ state
    #[case::plus_state(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Rotor::new(FRAC_1_SQRT_2, 0.0, -FRAC_1_SQRT_2, 0.0)
    )] // |+⟩ state
    #[case::minus_state(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(-FRAC_1_SQRT_2, 0.0),
        Rotor::new(FRAC_1_SQRT_2, 0.0, FRAC_1_SQRT_2, 0.0)
    )] // |-⟩ state
    #[case::plus_i_state(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(0.0, FRAC_1_SQRT_2),
        Rotor::new(FRAC_1_SQRT_2, FRAC_1_SQRT_2, 0.0, 0.0)
    )] // |+i⟩ state
    #[case::minus_i_state(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(0.0, -FRAC_1_SQRT_2),
        Rotor::new(FRAC_1_SQRT_2, -FRAC_1_SQRT_2, 0.0, 0.0)
    )] // |-i⟩ state
    fn test_new_method(
        #[case] alpha: Complex64,
        #[case] beta: Complex64,
        #[case] expected_rotor: Rotor,
    ) {
        let qubit = Qubit::new(alpha, beta).unwrap();
        assert!(qubit.rotor.approx_eq(&expected_rotor, 1e-10));
    }

    #[rstest]
    #[case::zero_state(
        Rotor::new(1.0, 0.0, 0.0, 0.0),
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0)
    )] // |0⟩ state
    #[case::one_state(
        Rotor::new(0.0, 0.0, 1.0, 0.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(-1.0, 0.0)
    )] // |1⟩ state
    #[case::plus_state(
        Rotor::new(FRAC_1_SQRT_2, 0.0, FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(-FRAC_1_SQRT_2, 0.0)
    )] // |+⟩ state
    #[case::minus_state(
        Rotor::new(FRAC_1_SQRT_2, 0.0, -FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0)
    )] // |-⟩ state
    #[case::plus_i_state(
        Rotor::new(FRAC_1_SQRT_2, FRAC_1_SQRT_2, 0.0, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(0.0, FRAC_1_SQRT_2)
    )] // |+i⟩ state
    #[case::minus_i_state(
        Rotor::new(FRAC_1_SQRT_2, -FRAC_1_SQRT_2, 0.0, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(0.0, -FRAC_1_SQRT_2)
    )] // |-i⟩ state
    fn test_complex_coefficients_method(
        #[case] rotor: Rotor,
        #[case] expected_alpha: Complex64,
        #[case] expected_beta: Complex64,
    ) {
        let qubit = Qubit { rotor };
        let (alpha, beta) = qubit.complex_coefficients();

        assert!((alpha - expected_alpha).norm() < 1e-10);
        assert!((beta - expected_beta).norm() < 1e-10);
    }
}
