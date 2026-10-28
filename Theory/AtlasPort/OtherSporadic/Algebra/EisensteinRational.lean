/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/EisensteinRational.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.Eisenstein

/-!
# Rational Eisenstein scalars

The integral Eisenstein algebra embeds in its rational counterpart.
Coordinate calculations establish positivity of its norm and show that the
two real pairings against one and omega determine a scalar.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/EisensteinRational.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with project module boundaries and rewritten imports.
-/

@[expose] public section

namespace Atlas.Algebra
open scoped QuadraticAlgebra

/-- The rational scalar algebra of the Eisenstein lattice. -/
abbrev EisensteinRational := QuadraticAlgebra ℚ (-1) (-1)

instance eisensteinRational_irreducible : Fact (∀ r : ℚ, r^2 ≠ -1 + (-1)*r) :=
  ⟨by intro r h; nlinarith [sq_nonneg (2*r+1)]⟩

def rationalOmega : EisensteinRational := QuadraticAlgebra.omega

/-- Real part in the complex embedding, as opposed to the coefficient of 1. -/
def eisensteinReal (z : EisensteinRational) : ℚ := z.re - z.im / 2

def eisensteinToRational : Eisenstein →+* EisensteinRational where
  toFun z := ⟨z.re, z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' := by intros; ext <;> simp
  map_mul' := by intros; ext <;> simp

theorem eisensteinToRational_injective : Function.Injective eisensteinToRational := by
  intro z w h
  have hr := congrArg QuadraticAlgebra.re h
  have hi := congrArg QuadraticAlgebra.im h
  change (z.re : ℚ) = w.re at hr
  change (z.im : ℚ) = w.im at hi
  ext
  · exact_mod_cast hr
  · exact_mod_cast hi

theorem rationalOmega_relation : rationalOmega ^ 2 + rationalOmega + 1 = 0 := by
  ext <;> norm_num [rationalOmega, QuadraticAlgebra.omega, pow_two]

theorem rationalOmega_cube : rationalOmega ^ 3 = 1 := by
  ext <;> norm_num [rationalOmega, QuadraticAlgebra.omega, pow_succ]

theorem rationalOmega_fixed_iff (z : EisensteinRational) :
    rationalOmega * z = z ↔ z = 0 := by
  constructor
  · intro h
    have hr := congrArg QuadraticAlgebra.re h
    have hi := congrArg QuadraticAlgebra.im h
    simp [rationalOmega, QuadraticAlgebra.omega] at hr hi
    ext <;> simp <;> linarith
  · rintro rfl; simp

theorem eisensteinReal_add (z w : EisensteinRational) :
    eisensteinReal (z+w) = eisensteinReal z + eisensteinReal w := by
  simp [eisensteinReal]; ring

theorem eisensteinReal_smul (a : ℚ) (z : EisensteinRational) :
    eisensteinReal (a • z) = a * eisensteinReal z := by
  simp [eisensteinReal]; ring

/-- The two real pairings with 1 and omega determine a scalar. -/
theorem eisensteinReal_ext (z w : EisensteinRational)
    (h : eisensteinReal z = eisensteinReal w)
    (ho : eisensteinReal (rationalOmega * z) = eisensteinReal (rationalOmega * w)) : z=w := by
  simp [eisensteinReal, rationalOmega, QuadraticAlgebra.omega] at h ho
  ext <;> linarith

theorem eisensteinReal_star_mul_self (z : EisensteinRational) :
    eisensteinReal (star z*z) = z.re^2-z.re*z.im+z.im^2 := by
  simp [eisensteinReal]; ring

theorem eisensteinReal_star_mul_self_nonneg (z : EisensteinRational) :
    0 ≤ eisensteinReal (star z*z) := by
  rw [eisensteinReal_star_mul_self]
  nlinarith [sq_nonneg (2*z.re-z.im), sq_nonneg z.im]

theorem eisensteinReal_star_mul_self_eq_zero (z : EisensteinRational) :
    eisensteinReal (star z*z) = 0 ↔ z=0 := by
  rw [eisensteinReal_star_mul_self]
  constructor
  · intro h
    have hi : z.im=0 := by nlinarith [sq_nonneg (2*z.re-z.im), sq_nonneg z.im]
    have hr : z.re=0 := by rw [hi] at h; nlinarith [sq_nonneg z.re]
    ext <;> simp [hr, hi]
  · rintro rfl; simp

end Atlas.Algebra
