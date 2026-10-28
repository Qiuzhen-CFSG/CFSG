/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/GoldenRational.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic

/-!
# The golden field and its positive coefficient functional

The quadratic algebra with τ² = 1 + τ is a field: a rational root would
make 5 a rational square. Its coefficient-of-one functional sends a square
to the sum of the squares of the two rational coordinates. This gives
positivity and nondegeneracy for the icosian trace-lattice construction.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/GoldenRational.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports and public module boundaries changed.
The field instance uses the irreducibility criterion of Mathlib 4.33 in place
of the upstream discriminant module. Definition bodies remain exposed for the coordinate calculations in consumers.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false

namespace Atlas.Algebra
open scoped QuadraticAlgebra

/-- The rational golden field, with distinguished root τ²=1+τ. -/
abbrev GoldenRational := QuadraticAlgebra ℚ 1 1

/-- The discriminant of the golden polynomial is not a rational square. -/
instance goldenRational_discriminant : Fact (¬ IsSquare ((1 : ℚ) ^ 2 + 4 * 1)) :=
  ⟨by norm_num⟩

/-- The golden polynomial has no rational root. This is the field-instance
criterion in Mathlib 4.33, expressed without the later discriminant API. -/
instance goldenRational_irreducible : Fact (∀ r : ℚ, r ^ 2 ≠ 1 + 1 * r) :=
  ⟨by
    intro r hr
    have hn : ¬ IsSquare (5 : ℚ) := by norm_num
    apply hn
    refine ⟨2 * r - 1, ?_⟩
    nlinarith⟩

def goldenTau : GoldenRational := QuadraticAlgebra.omega

def goldenSigma : GoldenRational := 1 - goldenTau

/-- The coefficient functional fixed in the icosian trace-lattice convention. -/
def goldenFunctional (z : GoldenRational) : ℚ := z.re

/-- Field trace, distinct from the chosen weighted functional. -/
def goldenTrace (z : GoldenRational) : ℚ := 2*z.re + z.im

def goldenAlpha : GoldenRational := ⟨3/5, -1/5⟩

theorem goldenTau_sq : goldenTau^2 = 1+goldenTau := by
  ext <;> norm_num [goldenTau, QuadraticAlgebra.omega, pow_two]

theorem goldenSigma_eq_star : goldenSigma = star goldenTau := by
  ext <;> simp [goldenSigma, goldenTau, QuadraticAlgebra.omega]

theorem goldenTau_mul_sigma : goldenTau*goldenSigma = -1 := by
  ext <;> norm_num [goldenSigma, goldenTau, QuadraticAlgebra.omega]

theorem goldenFunctional_add (x y : GoldenRational) :
    goldenFunctional (x+y)=goldenFunctional x+goldenFunctional y := rfl

theorem goldenFunctional_mul (x y : GoldenRational) :
    goldenFunctional (x*y)=x.re*y.re+x.im*y.im := by
  simp [goldenFunctional]

theorem goldenFunctional_sq (x : GoldenRational) :
    goldenFunctional (x^2)=x.re^2+x.im^2 := by
  simp [pow_two,goldenFunctional_mul]

theorem goldenFunctional_sq_nonneg (x : GoldenRational) :
    0 ≤ goldenFunctional (x^2) := by
  rw [goldenFunctional_sq]
  positivity

theorem goldenFunctional_sq_eq_zero (x : GoldenRational) :
    goldenFunctional (x^2)=0 ↔ x=0 := by
  rw [goldenFunctional_sq]
  constructor
  · intro h
    have hr : x.re=0 := by nlinarith [sq_nonneg x.re,sq_nonneg x.im]
    have hi : x.im=0 := by nlinarith [sq_nonneg x.re,sq_nonneg x.im]
    ext <;> simp [hr,hi]
  · rintro rfl; simp

theorem goldenFunctional_weighted_trace (x : GoldenRational) :
    goldenFunctional x=goldenTrace (goldenAlpha*x) := by
  simp [goldenFunctional,goldenTrace,goldenAlpha]
  ring

theorem goldenFunctional_pairing_nondegenerate (x : GoldenRational)
    (h : ∀ y, goldenFunctional (x*y)=0) : x=0 := by
  apply (goldenFunctional_sq_eq_zero x).mp
  simpa [pow_two] using h x

end Atlas.Algebra
