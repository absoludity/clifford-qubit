//! Clifford algebra-based quantum simulator.

use clifford_qubit::qubit::Qubit;
use qsc_eval::backend::Backend;
use rand::{SeedableRng, rngs::StdRng};

/// A quantum simulator using Clifford algebra to represent qubits.
pub struct CliffordSimulator {
    /// The qubits in the simulator
    pub qubits: Vec<Qubit>,
    /// Random number generator for measurements
    rng: StdRng,
}

impl Default for CliffordSimulator {
    fn default() -> Self {
        Self::new()
    }
}

impl CliffordSimulator {
    /// Creates a new Clifford simulator with no qubits.
    #[must_use]
    pub fn new() -> Self {
        Self {
            qubits: Vec::new(),
            rng: StdRng::from_entropy(),
        }
    }

    // Creates a new Clifford simulator with a specific random seed.
    // #[must_use]
    // pub fn with_seed(seed: u64) -> Self {
    //     Self {
    //         qubits: Vec::new(),
    //         rng: StdRng::seed_from_u64(seed),
    //     }
    // }
}

impl Backend for CliffordSimulator {
    type ResultType = bool;

    fn x(&mut self, target: usize) {
        if target >= self.qubits.len() {
            panic!(
                "Target qubit index {} is out of range (0..{})",
                target,
                self.qubits.len()
            );
        }
        let _ = self.qubits[target].x();
    }

    fn y(&mut self, target: usize) {
        if target >= self.qubits.len() {
            panic!(
                "Target qubit index {} is out of range (0..{})",
                target,
                self.qubits.len()
            );
        }
        let _ = self.qubits[target].y();
    }

    fn z(&mut self, target: usize) {
        if target >= self.qubits.len() {
            panic!(
                "Target qubit index {} is out of range (0..{})",
                target,
                self.qubits.len()
            );
        }
        let _ = self.qubits[target].z();
    }

    fn qubit_allocate(&mut self) -> usize {
        // Create a new qubit in the |0⟩ state using Default
        let qubit = Qubit::default();

        // Add to the end and return the index
        let id = self.qubits.len();
        self.qubits.push(qubit);
        id
    }

    fn qubit_release(&mut self, q: usize) -> bool {
        if q < self.qubits.len() {
            // Check if qubit is in |0⟩ state
            let (alpha, beta) = self.qubits[q].complex_coefficients();
            return (alpha.norm() - 1.0).abs() < 1e-10 && beta.norm() < 1e-10;
        }
        false
    }

    fn qubit_is_zero(&mut self, q: usize) -> bool {
        if q < self.qubits.len() {
            let (alpha, beta) = self.qubits[q].complex_coefficients();
            return (alpha.norm() - 1.0).abs() < 1e-10 && beta.norm() < 1e-10;
        }
        false
    }

    fn set_seed(&mut self, seed: Option<u64>) {
        if let Some(seed) = seed {
            self.rng = StdRng::seed_from_u64(seed);
        } else {
            self.rng = StdRng::from_entropy();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_qubit_allocation_and_x_gate() {
        let mut sim = CliffordSimulator::new();

        // Allocate a qubit (should be in |0⟩ state)
        let q = sim.qubit_allocate();
        assert!(sim.qubit_is_zero(q));

        // Apply X gate (should flip to |1⟩ state)
        sim.x(q);
        assert!(!sim.qubit_is_zero(q));

        // Release the qubit (should return false since it's in |1⟩ state)
        assert!(!sim.qubit_release(q));
    }
}
