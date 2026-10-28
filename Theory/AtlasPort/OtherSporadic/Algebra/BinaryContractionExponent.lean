/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/BinaryContractionExponent.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Data.Nat.ModEq

/-!
# BinaryContractionExponent

The parity of five binary exponents gives a nonnegative even excess, whose
half is at most two. The proof uses Presburger arithmetic.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/BinaryContractionExponent.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and explicit public imports.
-/

public section

namespace Atlas.Algebra

/-- Five binary exponents with prescribed binary parity have precisely the
nonnegative even excess needed in the quintic contraction. -/
theorem binary_contraction_exponent (e d₀ d₁ d₂ d₃ d₄ : ℕ)
    (he : e ≤ 1) (h₀ : d₀ ≤ 1) (h₁ : d₁ ≤ 1) (h₂ : d₂ ≤ 1)
    (h₃ : d₃ ≤ 1) (h₄ : d₄ ≤ 1)
    (hp : (d₀ + d₁ + d₂ + d₃ + d₄) % 2 = e) :
    e ≤ d₀ + d₁ + d₂ + d₃ + d₄ ∧
      d₀ + d₁ + d₂ + d₃ + d₄ - e =
        2 * ((d₀ + d₁ + d₂ + d₃ + d₄ - e) / 2) ∧
      (d₀ + d₁ + d₂ + d₃ + d₄ - e) / 2 ≤ 2 := by
  omega

end Atlas.Algebra
