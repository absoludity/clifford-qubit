# clifford-qubit

[![Crate](https://img.shields.io/crates/v/clifford-qubit.svg)](https://crates.io/crates/clifford-qubit)
[![API](https://docs.rs/clifford-qubit/badge.svg)](https://docs.rs/clifford-qubit)
[![License: MIT OR Apache-2.0](https://img.shields.io/badge/License-MIT%2FApache--2.0-blue.svg)](LICENSE-MIT)

A Rust library implementing quantum bits (qubits) using Clifford algebra.

## Overview

`clifford-qubit` provides a mathematical representation of qubits using Clifford algebra, specifically the even subalgebra of the 3D Clifford algebra. This approach offers an elegant geometric interpretation of quantum operations.

The library represents a qubit state |ψ⟩ = α|0⟩ + β|1⟩ using rotors from Clifford algebra, enabling efficient and intuitive implementation of quantum gates and operations.

## Features

- Pure Rust implementation of qubits using Clifford algebra
- Mathematically rigorous representation of quantum states
- Implementation of fundamental quantum gates (Pauli gates)
- Efficient conversion between complex coefficient and rotor representations

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
clifford-qubit = "0.1.0"
```

### Basic Example

```rust
use clifford_qubit::Qubit;
use clifford_qubit::gates::single::pauli;
use num::complex::Complex64;

// Create a qubit in the |0⟩ state
let mut qubit = Qubit::new(Complex64::new(1.0, 0.0), Complex64::new(0.0, 0.0)).unwrap();

// Apply the Pauli X gate (NOT gate)
qubit.x();

// Extract the complex coefficients
let (alpha, beta) = qubit.complex_coefficients();
assert!((alpha.norm() - 0.0).abs() < 1e-10);
assert!((beta.norm() - 1.0).abs() < 1e-10);
```

## Mathematical Background

This library represents qubits using the even subalgebra of the 3D Clifford algebra. A qubit state |ψ⟩ = α|0⟩ + β|1⟩ is mapped to a rotor:

α₀ + α₁Iz + -Iy(β₀ + β₁Iz) = α₀ + α₁Iz -β₀Iy + β₁Ix

This representation allows for elegant implementation of quantum gates as geometric operations in the Clifford algebra.

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
