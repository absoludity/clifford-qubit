//! Implementation of an array of qubits for multi-qubit quantum operations.

use crate::qubit::Qubit;
use std::fmt;

/// Represents an array of qubits for multi-qubit quantum operations.
///
/// This structure allows for efficient manipulation of multiple qubits
/// and provides methods for common multi-qubit operations.
#[derive(Debug, Clone, PartialEq)]
pub struct QubitArray {
    /// The array of qubits
    qubits: Vec<Qubit>,
    /// The coefficient for the entire array. Defaults to unity until there is entanglement.
    coefficient: f64,
}

impl QubitArray {
    /// Creates a new empty qubit array.
    ///
    /// # Returns
    ///
    /// An empty `QubitArray`
    #[must_use]
    pub const fn new() -> Self {
        Self {
            qubits: Vec::new(),
            coefficient: 1.0,
        }
    }

    /// Creates a new qubit array with the specified capacity.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The initial capacity of the array
    ///
    /// # Returns
    ///
    /// A `QubitArray` with the specified capacity
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            qubits: Vec::with_capacity(capacity),
            coefficient: 1.0,
        }
    }

    /// Creates a new qubit array from a vector of qubits.
    ///
    /// # Arguments
    ///
    /// * `qubits` - A vector of qubits
    ///
    /// # Returns
    ///
    /// A `QubitArray` containing the provided qubits
    #[must_use]
    pub const fn from_qubits(qubits: Vec<Qubit>) -> Self {
        Self {
            qubits,
            coefficient: 1.0,
        }
    }

    /// Creates a new qubit array with all qubits in the |0⟩ state.
    ///
    /// # Arguments
    ///
    /// * `size` - The number of qubits to create
    ///
    /// # Returns
    ///
    /// A `QubitArray` with `size` qubits all in the |0⟩ state
    #[must_use]
    pub fn zeros(size: usize) -> Self {
        let qubits = vec![Qubit::default(); size];
        Self {
            qubits,
            coefficient: 1.0,
        }
    }

    /// Returns the number of qubits in the array.
    ///
    /// # Returns
    ///
    /// The number of qubits
    #[must_use]
    pub fn len(&self) -> usize {
        self.qubits.len()
    }

    /// Returns whether the array is empty.
    ///
    /// # Returns
    ///
    /// `true` if the array contains no qubits
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.qubits.is_empty()
    }

    /// Adds a qubit to the end of the array.
    ///
    /// # Arguments
    ///
    /// * `qubit` - The qubit to add
    pub fn push(&mut self, qubit: Qubit) {
        self.qubits.push(qubit);
    }

    /// Gets a reference to the qubit at the specified index.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the qubit to retrieve
    ///
    /// # Returns
    ///
    /// A reference to the qubit at the specified index, or `None` if out of bounds
    #[must_use]
    pub fn get(&self, index: usize) -> Option<&Qubit> {
        self.qubits.get(index)
    }

    /// Gets a mutable reference to the qubit at the specified index.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the qubit to retrieve
    ///
    /// # Returns
    ///
    /// A mutable reference to the qubit at the specified index, or `None` if out of bounds
    pub fn get_mut(&mut self, index: usize) -> Option<&mut Qubit> {
        self.qubits.get_mut(index)
    }

    /// Returns the coefficient of the qubit array.
    ///
    /// # Returns
    ///
    /// The coefficient as an f64
    #[must_use]
    pub const fn coefficient(&self) -> f64 {
        self.coefficient
    }

    /// Applies the Pauli X gate to the qubit at the specified index.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the qubit to apply the gate to
    ///
    /// # Returns
    ///
    /// `Ok(())` if successful, or an error if the index is out of bounds
    ///
    /// # Errors
    ///
    /// Returns an error if the index is out of bounds
    pub fn x(&mut self, index: usize) -> Result<(), String> {
        self.qubits.get_mut(index).map_or_else(
            || Err(format!("Index {index} is out of bounds")),
            |qubit| {
                qubit.x();
                Ok(())
            },
        )
    }

    /// Applies the Pauli Y gate to the qubit at the specified index.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the qubit to apply the gate to
    ///
    /// # Returns
    ///
    /// `Ok(())` if successful, or an error if the index is out of bounds
    ///
    /// # Errors
    ///
    /// Returns an error if the index is out of bounds
    pub fn y(&mut self, index: usize) -> Result<(), String> {
        self.qubits.get_mut(index).map_or_else(
            || Err(format!("Index {index} is out of bounds")),
            |qubit| {
                qubit.y();
                Ok(())
            },
        )
    }

    /// Applies the Pauli Z gate to the qubit at the specified index.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the qubit to apply the gate to
    ///
    /// # Returns
    ///
    /// `Ok(())` if successful, or an error if the index is out of bounds
    ///
    /// # Errors
    ///
    /// Returns an error if the index is out of bounds
    pub fn z(&mut self, index: usize) -> Result<(), String> {
        self.qubits.get_mut(index).map_or_else(
            || Err(format!("Index {index} is out of bounds")),
            |qubit| {
                qubit.z();
                Ok(())
            },
        )
    }

    /// Converts the qubit array to a vector of qubits.
    ///
    /// This consumes the `QubitArray` and returns the underlying vector.
    ///
    /// # Returns
    ///
    /// A vector containing all the qubits
    #[must_use]
    pub fn into_vec(self) -> Vec<Qubit> {
        self.qubits
    }
}

impl Default for QubitArray {
    /// Creates an empty qubit array.
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for QubitArray {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.coefficient)?;
        for qubit in &self.qubits {
            write!(f, "({})", qubit.rotor())?;
        }
        Ok(())
    }
}

impl std::ops::Index<usize> for QubitArray {
    type Output = Qubit;

    fn index(&self, index: usize) -> &Self::Output {
        &self.qubits[index]
    }
}

impl std::ops::IndexMut<usize> for QubitArray {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.qubits[index]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num::complex::Complex64;
    use rstest::rstest;

    #[test]
    fn test_new() {
        let array = QubitArray::new();
        assert!(array.is_empty());
        assert_eq!(array.len(), 0);
    }

    #[test]
    fn test_with_capacity() {
        let array = QubitArray::with_capacity(10);
        assert!(array.is_empty());
        assert_eq!(array.len(), 0);
    }

    #[test]
    fn test_zeros() {
        let array = QubitArray::zeros(3);
        assert_eq!(array.len(), 3);

        for i in 0..array.len() {
            let (alpha, beta) = array[i].complex_coefficients();
            assert!((alpha - Complex64::new(1.0, 0.0)).norm() < 1e-10);
            assert!((beta - Complex64::new(0.0, 0.0)).norm() < 1e-10);
        }
    }

    #[test]
    fn test_push() {
        let mut array = QubitArray::new();
        let qubit = Qubit::default();

        array.push(qubit);
        assert_eq!(array.len(), 1);
    }

    #[test]
    fn test_indexing() {
        let mut array = QubitArray::zeros(3);

        // Test immutable indexing
        let first = &array[0];
        let (alpha, _) = first.complex_coefficients();
        assert!((alpha - Complex64::new(1.0, 0.0)).norm() < 1e-10);

        // Test mutable indexing
        array[1].x();
        let (alpha, beta) = array[1].complex_coefficients();
        assert!((alpha - Complex64::new(0.0, 0.0)).norm() < 1e-10);
        assert!((beta - Complex64::new(1.0, 0.0)).norm() < 1e-10);
    }

    #[test]
    fn test_gate_operations() {
        let mut array = QubitArray::zeros(3);

        // Test single qubit operations
        assert!(array.x(0).is_ok());
        assert!(array.y(1).is_ok());
        assert!(array.z(2).is_ok());

        // Test out of bounds
        assert!(array.x(10).is_err());

        // Verify X gate worked
        let (alpha, beta) = array[0].complex_coefficients();
        assert!((alpha - Complex64::new(0.0, 0.0)).norm() < 1e-10);
        assert!((beta - Complex64::new(1.0, 0.0)).norm() < 1e-10);
    }

    #[test]
    fn test_coefficient() {
        let array = QubitArray::new();
        assert_eq!(array.coefficient(), 1.0);

        let array = QubitArray::zeros(3);
        assert_eq!(array.coefficient(), 1.0);

        let array = QubitArray::with_capacity(10);
        assert_eq!(array.coefficient(), 1.0);
    }

    #[rstest]
    #[case::empty_array(QubitArray::new(), "1")]
    #[case::single_zero_qubit(QubitArray::zeros(1), "1(1)")]
    #[case::three_zero_qubits(QubitArray::zeros(3), "1(1)(1)(1)")]
    #[case::two_zero_qubits(QubitArray::zeros(2), "1(1)(1)")]
    #[case::mixed_qubits({
        let mut array = QubitArray::zeros(2);
        array.x(1).unwrap();
        array
    }, "1(1)(-1Iy)")]
    fn test_display(#[case] array: QubitArray, #[case] expected: &str) {
        assert_eq!(format!("{}", array), expected);
    }
}
