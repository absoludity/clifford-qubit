//! Display implementations for the Qubit type.

use crate::qubit::Qubit;
use std::fmt;

impl fmt::Display for Qubit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            // Display in Dirac notation: α|0⟩ + β|1⟩
            format_dirac(self, f)
        } else {
            // Display as rotor (current behavior)
            format_rotor(self, f)
        }
    }
}

/// Formats the qubit as a rotor with optional precision.
fn format_rotor(qubit: &Qubit, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if let Some(precision) = f.precision() {
        write!(f, "{:.prec$}", qubit.rotor, prec = precision)
    } else {
        write!(f, "{}", qubit.rotor)
    }
}

/// Formats the qubit in Dirac notation with optional precision.
fn format_dirac(qubit: &Qubit, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let (alpha, beta) = qubit.complex_coefficients();
    let mut has_terms = false;

    // Handle the α|0⟩ term
    if alpha.norm() > 1e-10 {
        format_coefficient(alpha, "|0⟩", f)?;
        has_terms = true;
    }

    // Handle the β|1⟩ term
    if beta.norm() > 1e-10 {
        if has_terms {
            write!(f, " + ")?;
        }
        format_coefficient(beta, "|1⟩", f)?;
        has_terms = true;
    }

    // Handle the zero state case
    if !has_terms {
        write!(f, "0")?;
    }

    Ok(())
}

/// Formats a complex coefficient with the given state label.
fn format_coefficient(
    coeff: num::complex::Complex64,
    state: &str,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    if coeff.im.abs() < 1e-10 {
        // Purely real coefficient
        if let Some(precision) = f.precision() {
            write!(f, "({:.prec$}){}", coeff.re, state, prec = precision)
        } else {
            write!(f, "({}){}", coeff.re, state)
        }
    } else if coeff.re.abs() < 1e-10 {
        // Purely imaginary coefficient
        if let Some(precision) = f.precision() {
            write!(f, "({:.prec$}i){}", coeff.im, state, prec = precision)
        } else {
            write!(f, "({}i){}", coeff.im, state)
        }
    } else {
        // Complex coefficient
        if let Some(precision) = f.precision() {
            write!(
                f,
                "({:.prec$}{:+.prec$}i){}",
                coeff.re,
                coeff.im,
                state,
                prec = precision
            )
        } else {
            write!(f, "({}){}", coeff, state)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::qubit::Qubit;
    use num::complex::Complex64;
    use rstest::rstest;
    use std::f64::consts::FRAC_1_SQRT_2;

    #[rstest]
    #[case::zero_state(
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0),
        "1",
        "1.000",
        "(1)|0⟩",
        "(1.000)|0⟩"
    )] // |0⟩ state
    #[case::one_state(
        Complex64::new(0.0, 0.0),
        Complex64::new(1.0, 0.0),
        "-1Iy",
        "-1.000Iy",
        "(1)|1⟩",
        "(1.000)|1⟩"
    )] // |1⟩ state
    #[case::plus_state(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        "0.7071067811865476 - 0.7071067811865476Iy",
        "0.707 - 0.707Iy",
        "(0.7071067811865476)|0⟩ + (0.7071067811865476)|1⟩",
        "(0.707)|0⟩ + (0.707)|1⟩"
    )] // |+⟩ state
    #[case::minus_state(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(-FRAC_1_SQRT_2, 0.0),
        "0.7071067811865476 + 0.7071067811865476Iy",
        "0.707 + 0.707Iy",
        "(0.7071067811865476)|0⟩ + (-0.7071067811865476)|1⟩",
        "(0.707)|0⟩ + (-0.707)|1⟩"
    )] // |-⟩ state
    #[case::plus_i_state(
        Complex64::new(FRAC_1_SQRT_2, 0.0),
        Complex64::new(0.0, FRAC_1_SQRT_2),
        "0.7071067811865476 + 0.7071067811865476Ix",
        "0.707 + 0.707Ix",
        "(0.7071067811865476)|0⟩ + (0.7071067811865476i)|1⟩",
        "(0.707)|0⟩ + (0.707i)|1⟩"
    )] // |+i⟩ state
    #[case::complex_state(
        Complex64::new(0.5, 0.5),
        Complex64::new(0.5, -0.5),
        "0.5 - 0.5Ix - 0.5Iy + 0.5Iz",
        "0.500 - 0.500Ix - 0.500Iy + 0.500Iz",
        "(0.5+0.5i)|0⟩ + (0.5-0.5i)|1⟩",
        "(0.500+0.500i)|0⟩ + (0.500-0.500i)|1⟩"
    )] // Complex coefficients state
    fn test_display_formats(
        #[case] alpha: Complex64,
        #[case] beta: Complex64,
        #[case] expected_rotor: &str,
        #[case] expected_rotor_precision: &str,
        #[case] expected_dirac: &str,
        #[case] expected_dirac_precision: &str,
    ) {
        let qubit = Qubit::new(alpha, beta).unwrap();

        // Test rotor format (default)
        assert_eq!(format!("{}", qubit), expected_rotor);

        // Test rotor format with 3 decimal places
        assert_eq!(format!("{:.3}", qubit), expected_rotor_precision);

        // Test Dirac format (alternate) without precision
        assert_eq!(format!("{:#}", qubit), expected_dirac);

        // Test Dirac format (alternate) with 3 decimal places
        assert_eq!(format!("{:#.3}", qubit), expected_dirac_precision);
    }

    #[test]
    fn test_precision_behavior() {
        let qubit = Qubit::new(
            Complex64::new(FRAC_1_SQRT_2, 0.0),
            Complex64::new(FRAC_1_SQRT_2, 0.0),
        )
        .unwrap();

        // Test rotor format precision
        assert_eq!(
            format!("{}", qubit),
            "0.7071067811865476 - 0.7071067811865476Iy"
        );
        assert_eq!(format!("{:.2}", qubit), "0.71 - 0.71Iy");
        assert_eq!(format!("{:.4}", qubit), "0.7071 - 0.7071Iy");

        // Test Dirac format precision
        assert_eq!(
            format!("{:#}", qubit),
            "(0.7071067811865476)|0⟩ + (0.7071067811865476)|1⟩"
        );
        assert_eq!(format!("{:#.2}", qubit), "(0.71)|0⟩ + (0.71)|1⟩");
        assert_eq!(format!("{:#.4}", qubit), "(0.7071)|0⟩ + (0.7071)|1⟩");
    }

    #[test]
    fn test_zero_state() {
        let qubit = Qubit::new(Complex64::new(0.0, 0.0), Complex64::new(0.0, 0.0));

        // This should fail to create due to normalization, but if we had a zero state:
        // assert_eq!(format!("{:#}", qubit), "0");

        // Instead, test a very small coefficient state that should show as "0"
        // This is more of a conceptual test since we can't actually create unnormalized qubits
        assert!(qubit.is_err()); // Confirms we can't create zero states
    }

    #[test]
    fn test_purely_real_coefficients() {
        let qubit = Qubit::new(Complex64::new(0.6, 0.0), Complex64::new(0.8, 0.0)).unwrap();

        assert_eq!(format!("{:#}", qubit), "(0.6)|0⟩ + (0.8)|1⟩");
        assert_eq!(format!("{:#.1}", qubit), "(0.6)|0⟩ + (0.8)|1⟩");
    }

    #[test]
    fn test_purely_imaginary_coefficients() {
        let qubit = Qubit::new(Complex64::new(0.0, 0.6), Complex64::new(0.0, 0.8)).unwrap();

        assert_eq!(format!("{:#}", qubit), "(0.6i)|0⟩ + (0.8i)|1⟩");
        assert_eq!(format!("{:#.1}", qubit), "(0.6i)|0⟩ + (0.8i)|1⟩");
    }
}
