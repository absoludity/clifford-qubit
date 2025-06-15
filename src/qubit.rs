//! Implementation of a quantum bit (qubit) using Clifford algebra.

use clifford_3_even::Rotor;
use num::complex::Complex64;
use std::fmt;

use crate::error::QubitError;

/// Represents a quantum bit (qubit).
///
/// A qubit is represented by two complex coefficients α and β such that:
/// |ψ⟩ = α|0⟩ + β|1⟩
/// where |α|² + |β|² = 1
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Qubit {
    /// The underlying rotor representation
    pub rotor: Rotor,
}

impl Default for Qubit {
    /// Creates a default qubit in the |0⟩ state.
    fn default() -> Self {
        Self::new(Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0))
            .expect("Default qubit creation should never fail")
    }
}

impl fmt::Display for Qubit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.rotor)
    }
}

impl Qubit {
    /// Creates a new qubit from complex coefficients for |0⟩ and |1⟩ states.
    ///
    /// # Arguments
    ///
    /// * `alpha` - Complex coefficient for the |0⟩ state
    /// * `beta` - Complex coefficient for the |1⟩ state
    ///
    /// where
    /// a_0 = α₀,
    /// a_z = α₁
    /// a_y = -β₀
    /// a_x = β₁
    /// according to the normal map of quantum complex coefficients to
    /// the Cl(3) even sub-algebra (link to Doran etc.)
    ///
    /// # Returns
    ///
    /// Ok(Qubit) if the coefficients satisfy |α|² + |β|² = 1, Err(QubitError) otherwise
    #[must_use]
    pub fn new(alpha: Complex64, beta: Complex64) -> Result<Self, QubitError> {
        // Check normalization condition: |α|² + |β|² = 1
        let norm_squared = alpha.norm_sqr() + beta.norm_sqr();
        if (norm_squared - 1.0).abs() > 1e-10 {
            return Err(QubitError::NotNormalized { norm_squared });
        }

        let rotor = Rotor::new(alpha.re, beta.im, -beta.re, alpha.im);

        Ok(Self { rotor })
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
    /// Ok(Qubit) if the rotor is normalized, Err(QubitError) otherwise
    #[must_use]
    pub fn from_rotor(rotor: Rotor) -> Result<Self, QubitError> {
        // Check normalization condition: |rotor|² = 1
        let norm_squared = rotor.magnitude_squared();
        if (norm_squared - 1.0).abs() > 1e-10 {
            return Err(QubitError::NotNormalized { norm_squared });
        }

        Ok(Self { rotor })
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

    /// Applies the Pauli X gate to this qubit, modifying it in place.
    ///
    /// The Pauli X gate flips the state of a qubit:
    /// X|0⟩ = |1⟩ and X|1⟩ = |0⟩
    ///
    /// # Returns
    ///
    /// A mutable reference to self for method chaining
    pub fn x(&mut self) -> &mut Self {
        crate::gates::single::pauli::x(self)
    }

    /// Applies the Pauli Y gate to this qubit, modifying it in place.
    ///
    /// The Pauli Y gate is a rotation around the Y-axis:
    /// Y|0⟩ = i|1⟩ and Y|1⟩ = -i|0⟩
    ///
    /// # Returns
    ///
    /// A mutable reference to self for method chaining
    pub fn y(&mut self) -> &mut Self {
        crate::gates::single::pauli::y(self)
    }

    /// Applies the Pauli Z gate to this qubit, modifying it in place.
    ///
    /// The Pauli Z gate is a rotation around the Z-axis:
    /// Z|0⟩ = |0⟩ and Z|1⟩ = -|1⟩
    ///
    /// # Returns
    ///
    /// A mutable reference to self for method chaining
    pub fn z(&mut self) -> &mut Self {
        crate::gates::single::pauli::z(self)
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
        let coefficients = qubit.complex_coefficients();
        assert_eq!(coefficients.0, alpha);
        assert_eq!(coefficients.1, beta);
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

    #[test]
    fn test_new_method_unnormalized_coefficients() {
        // Test with unnormalized coefficients
        let alpha = Complex64::new(1.0, 0.0);
        let beta = Complex64::new(1.0, 0.0); // |α|² + |β|² = 2, not 1

        let result = Qubit::new(alpha, beta);
        assert!(result.is_err());

        if let Err(QubitError::NotNormalized { norm_squared }) = result {
            assert!((norm_squared - 2.0).abs() < 1e-10);
        } else {
            panic!("Expected NotNormalized error");
        }
    }

    #[rstest]
    #[case::zero_state(Rotor::new(1.0, 0.0, 0.0, 0.0))] // |0⟩ state
    #[case::one_state(Rotor::new(0.0, 0.0, -1.0, 0.0))] // |1⟩ state
    #[case::plus_state(Rotor::new(FRAC_1_SQRT_2, 0.0, -FRAC_1_SQRT_2, 0.0))] // |+⟩ state
    #[case::minus_state(Rotor::new(FRAC_1_SQRT_2, 0.0, FRAC_1_SQRT_2, 0.0))] // |-⟩ state
    fn test_from_rotor_normalized(#[case] rotor: Rotor) {
        let result = Qubit::from_rotor(rotor);
        assert!(result.is_ok());
        let qubit = result.unwrap();
        assert!(qubit.rotor.approx_eq(&rotor, 1e-10));
    }

    #[test]
    fn test_from_rotor_unnormalized() {
        // Test with unnormalized rotor
        let unnormalized_rotor = Rotor::new(2.0, 0.0, 0.0, 0.0); // |rotor|² = 4, not 1

        let result = Qubit::from_rotor(unnormalized_rotor);
        assert!(result.is_err());

        if let Err(QubitError::NotNormalized { norm_squared }) = result {
            assert!((norm_squared - 4.0).abs() < 1e-10);
        } else {
            panic!("Expected NotNormalized error");
        }
    }
}
