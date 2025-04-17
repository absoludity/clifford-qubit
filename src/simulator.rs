//! Clifford algebra-based quantum simulator.

use crate::qubit::Qubit;
use num::complex::Complex64;
use num_bigint::BigUint;
use rand::{SeedableRng, rngs::StdRng};

/// The trait that must be implemented by a quantum backend, whose functions
/// will be invoked when quantum intrinsics are called.
/// Taken from:
/// https://github.com/microsoft/qsharp/blob/04ac1a4a19449d88aff782d8098782041e033d05/compiler/qsc_eval/src/backend.rs#L17-L112
/// as it's not available in a crate.
pub trait Backend {
    type ResultType;

    fn ccx(&mut self, _ctl0: usize, _ctl1: usize, _q: usize) {
        unimplemented!("ccx gate");
    }
    fn cx(&mut self, _ctl: usize, _q: usize) {
        unimplemented!("cx gate");
    }
    fn cy(&mut self, _ctl: usize, _q: usize) {
        unimplemented!("cy gate");
    }
    fn cz(&mut self, _ctl: usize, _q: usize) {
        unimplemented!("cz gate");
    }
    fn h(&mut self, _q: usize) {
        unimplemented!("h gate");
    }
    fn m(&mut self, _q: usize) -> Self::ResultType {
        unimplemented!("m operation");
    }
    fn mresetz(&mut self, _q: usize) -> Self::ResultType {
        unimplemented!("mresetz operation");
    }
    fn reset(&mut self, _q: usize) {
        unimplemented!("reset gate");
    }
    fn rx(&mut self, _theta: f64, _q: usize) {
        unimplemented!("rx gate");
    }
    fn rxx(&mut self, _theta: f64, _q0: usize, _q1: usize) {
        unimplemented!("rxx gate");
    }
    fn ry(&mut self, _theta: f64, _q: usize) {
        unimplemented!("ry gate");
    }
    fn ryy(&mut self, _theta: f64, _q0: usize, _q1: usize) {
        unimplemented!("ryy gate");
    }
    fn rz(&mut self, _theta: f64, _q: usize) {
        unimplemented!("rz gate");
    }
    fn rzz(&mut self, _theta: f64, _q0: usize, _q1: usize) {
        unimplemented!("rzz gate");
    }
    fn sadj(&mut self, _q: usize) {
        unimplemented!("sadj gate");
    }
    fn s(&mut self, _q: usize) {
        unimplemented!("s gate");
    }
    fn swap(&mut self, _q0: usize, _q1: usize) {
        unimplemented!("swap gate");
    }
    fn tadj(&mut self, _q: usize) {
        unimplemented!("tadj gate");
    }
    fn t(&mut self, _q: usize) {
        unimplemented!("t gate");
    }
    fn x(&mut self, _q: usize) {
        unimplemented!("x gate");
    }
    fn y(&mut self, _q: usize) {
        unimplemented!("y gate");
    }
    fn z(&mut self, _q: usize) {
        unimplemented!("z gate");
    }
    fn qubit_allocate(&mut self) -> usize {
        unimplemented!("qubit_allocate operation");
    }
    fn qubit_release(&mut self, _q: usize) -> bool {
        unimplemented!("qubit_release operation");
    }
    fn qubit_swap_id(&mut self, _q0: usize, _q1: usize) {
        unimplemented!("qubit_swap_id operation");
    }
    fn capture_quantum_state(&mut self) -> (Vec<(BigUint, Complex64)>, usize) {
        unimplemented!("capture_quantum_state operation");
    }
    fn qubit_is_zero(&mut self, _q: usize) -> bool {
        unimplemented!("qubit_is_zero operation");
    }
    fn set_seed(&mut self, _seed: Option<u64>) {}
}

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

    /// Creates a new Clifford simulator with a specific random seed.
    #[must_use]
    pub fn with_seed(seed: u64) -> Self {
        Self {
            qubits: Vec::new(),
            rng: StdRng::seed_from_u64(seed),
        }
    }
}

impl Backend for CliffordSimulator {
    type ResultType = bool;

    fn x(&mut self, target: usize) {
        if target >= self.qubits.len() {
            panic!("Target qubit index {} is out of range (0..{})", target, self.qubits.len());
        }
        let _ = self.qubits[target].x();
    }
    
    fn y(&mut self, target: usize) {
        if target >= self.qubits.len() {
            panic!("Target qubit index {} is out of range (0..{})", target, self.qubits.len());
        }
        let _ = self.qubits[target].y();
    }
    
    fn z(&mut self, target: usize) {
        if target >= self.qubits.len() {
            panic!("Target qubit index {} is out of range (0..{})", target, self.qubits.len());
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
