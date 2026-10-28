/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/BinaryWalsh.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Binary Walsh coefficients

Integer-valued binary characters give Walsh coefficients. Character
orthogonality and multiplicativity control their sums and constant phases.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/BinaryWalsh.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for the source computational interfaces.
-/

@[expose] public section

namespace Atlas.Algebra

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The integer-valued sign of a binary value. -/
def binaryWalshSign (b : ZMod 2) : ℤ := if b = 0 then 1 else -1

@[simp] theorem binaryWalshSign_zero : binaryWalshSign 0 = 1 := rfl
@[simp] theorem binaryWalshSign_one : binaryWalshSign 1 = -1 := by decide

theorem binaryWalshSign_add (a b : ZMod 2) :
    binaryWalshSign (a + b) = binaryWalshSign a * binaryWalshSign b := by
  revert a b
  decide +kernel

@[simp] theorem binaryWalshSign_eq_one (b : ZMod 2) : binaryWalshSign b = 1 ↔ b = 0 := by
  fin_cases b <;> norm_num [binaryWalshSign]

theorem binaryWalshSign_sq (b : ZMod 2) : binaryWalshSign b ^ 2 = 1 := by
  fin_cases b <;> norm_num [binaryWalshSign]

variable {V : Type*} [AddCommGroup V]

/-- A binary additive functional, viewed as an actual additive character. -/
def binaryWalshChar (a : V →+ ZMod 2) : AddChar V ℤ where
  toFun x := binaryWalshSign (a x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [map_add, binaryWalshSign_add]

@[simp] theorem binaryWalshChar_apply (a : V →+ ZMod 2) (x : V) :
    binaryWalshChar a x = binaryWalshSign (a x) := rfl

theorem binaryWalshChar_eq_zero (a : V →+ ZMod 2) : binaryWalshChar a = 0 ↔ a = 0 := by
  constructor
  · intro h
    ext x
    have hx := congrArg (fun f : AddChar V ℤ => f x) h
    exact (binaryWalshSign_eq_one _).mp hx
  · rintro rfl
    ext x
    simp

variable [Fintype V]

/-- Character orthogonality, reused directly from mathlib's additive characters. -/
theorem binaryWalshChar_sum (a : V →+ ZMod 2) :
    ∑ x, binaryWalshSign (a x) = if a = 0 then (Fintype.card V : ℤ) else 0 := by
  classical
  simpa only [binaryWalshChar_apply, binaryWalshChar_eq_zero] using
    AddChar.sum_eq_ite (binaryWalshChar a)

/-- Walsh coefficients are defined for arbitrary binary functions. Quadratic
normalization is imposed by the later quadratic-map interface. -/
def binaryWalsh (q : V → ZMod 2) (a : V →+ ZMod 2) : ℤ :=
  ∑ x, binaryWalshSign (q x + a x)

/-- Adding a constant is a separate scalar sign, not part of the polar form. -/
theorem binaryWalsh_add_constant (q : V → ZMod 2) (a : V →+ ZMod 2) (c : ZMod 2) :
    binaryWalsh (fun x => q x + c) a = binaryWalshSign c * binaryWalsh q a := by
  simp only [binaryWalsh, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [show q x + c + a x = c + (q x + a x) by ac_rfl, binaryWalshSign_add]

end Atlas.Algebra
