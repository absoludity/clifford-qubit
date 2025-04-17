//! Testing utilities for comparing CliffordSimulator against matrix-based
//! implementations.

#[cfg(test)]
mod tests {
    use quantum_sparse_sim::QuantumSim;

    use crate::simulator::Backend;
    use crate::simulator::CliffordSimulator;

    use num_bigint::BigUint;

    /// Compares the state of a single qubit in CliffordSimulator with the state
    /// in QuantumSim.
    ///
    /// This function applies the same operations to both simulators and then
    /// compares the resulting states.
    fn assert_qubit_states_equal<F, G>(clifford_op: F, sparse_op: G)
    where
        F: FnOnce(&mut CliffordSimulator),
        G: FnOnce(&mut QuantumSim),
    {
        // Initialize CliffordSimulator
        let mut clifford_sim = CliffordSimulator::new();

        // Initialize QuantumSim
        let mut sparse_sim = QuantumSim::new(None);

        // Allocate a single qubit in each simulator
        clifford_sim.qubit_allocate();
        let _ = sparse_sim.allocate();

        // Apply operations
        clifford_op(&mut clifford_sim);
        sparse_op(&mut sparse_sim);

        // Get the state from QuantumSim
        let (sparse_state, _) = sparse_sim.get_state();

        // Get the state from CliffordSimulator's qubit
        let (alpha, beta) = clifford_sim.qubits[0].complex_coefficients();

        // Convert to the same format as QuantumSim for comparison
        let mut clifford_state = Vec::new();
        if alpha.norm_sqr() > 1e-10 {
            clifford_state.push((BigUint::from(0u8), alpha));
        }
        if beta.norm_sqr() > 1e-10 {
            clifford_state.push((BigUint::from(1u8), beta));
        }

        // Compare the states
        assert_eq!(
            clifford_state.len(),
            sparse_state.len(),
            "State vector size mismatch: Clifford={}, Sparse={}",
            clifford_state.len(),
            sparse_state.len()
        );

        // For a single qubit, we can directly compare the states without sorting
        // There can only be at most two basis states: |0⟩ and |1⟩
        for (c_state, s_state) in clifford_state.iter().zip(sparse_state.iter()) {
            let (c_idx, c_amp) = c_state;
            let (s_idx, s_amp) = s_state;
            
            assert_eq!(
                c_idx, s_idx,
                "State index mismatch: Clifford={}, Sparse={}",
                c_idx, s_idx
            );

            // Compare amplitudes (allowing for small numerical differences)
            let amp_diff = (c_amp - s_amp).norm();
            assert!(
                amp_diff < 1e-9,
                "State amplitude mismatch for index {}: Clifford={}, Sparse={}, diff={}",
                c_idx,
                c_amp,
                s_amp,
                amp_diff
            );
        }
    }

    #[test]
    fn test_x_gate() {
        assert_qubit_states_equal(
            |sim| {
                sim.x(0);
            },
            |sim| {
                sim.x(0);
            },
        );
    }

    #[test]
    fn test_x_gate_twice() {
        assert_qubit_states_equal(
            |sim| {
                sim.x(0);
                sim.x(0);
            },
            |sim| {
                sim.x(0);
                sim.x(0);
            },
        );
    }
    
    #[test]
    fn test_y_gate() {
        assert_qubit_states_equal(
            |sim| {
                sim.y(0);
            },
            |sim| {
                sim.y(0);
            },
        );
    }
    
    #[test]
    fn test_z_gate() {
        assert_qubit_states_equal(
            |sim| {
                sim.z(0);
            },
            |sim| {
                sim.z(0);
            },
        );
    }
    
    #[test]
    fn test_xyz_sequence() {
        assert_qubit_states_equal(
            |sim| {
                sim.x(0);
                sim.y(0);
                sim.z(0);
            },
            |sim| {
                sim.x(0);
                sim.y(0);
                sim.z(0);
            },
        );
    }
}
