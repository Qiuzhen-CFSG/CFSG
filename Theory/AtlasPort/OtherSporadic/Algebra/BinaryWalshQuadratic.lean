/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/BinaryWalshQuadratic.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.BinaryWalsh
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.Ring

/-!
# Quadratic Walsh radicals

The kernel of the polar bilinear form is the quadratic radical.
Restricting a quadratic function plus a linear functional to this radical
gives the character that detects compatibility.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/BinaryWalshQuadratic.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for the source computational interfaces.
-/

@[expose] public section

namespace Atlas.Algebra

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The radical is the kernel of the actual polar bilinear map. -/
def binaryWalshRadical (q : QuadraticMap (ZMod 2) V (ZMod 2)) : Submodule (ZMod 2) V :=
  LinearMap.ker q.polarBilin

theorem binaryWalsh_quadratic_zero (q : QuadraticMap (ZMod 2) V (ZMod 2)) : q 0 = 0 :=
  map_zero q

theorem binaryWalsh_polar_formula (q : QuadraticMap (ZMod 2) V (ZMod 2)) (x y : V) :
    q.polarBilin x y = q (x + y) + q x + q y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, sub_eq_add_neg,
    CharTwo.neg_eq]

theorem binaryWalsh_quadratic_add (q : QuadraticMap (ZMod 2) V (ZMod 2)) (x y : V) :
    q (x + y) = q x + q y + q.polarBilin x y := by
  rw [binaryWalsh_polar_formula]
  calc
    q (x + y) = q (x + y) + (q x + q x) + (q y + q y) := by
      rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero, add_zero]
    _ = _ := by ac_rfl

theorem binaryWalsh_mem_radical (q : QuadraticMap (ZMod 2) V (ZMod 2)) (x : V) :
    x ∈ binaryWalshRadical q ↔ ∀ y, q.polarBilin x y = 0 := by
  change q.polarBilin x = 0 ↔ _
  exact LinearMap.ext_iff

/-- The quadratic function plus a linear functional restricts to an additive
character on the polar radical. The quadratic-map type explicitly forces q(0)=0. -/
def binaryWalshRadicalChar (q : QuadraticMap (ZMod 2) V (ZMod 2))
    (a : V →+ ZMod 2) : AddChar (binaryWalshRadical q) ℤ where
  toFun x := binaryWalshSign (q x + a x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    change binaryWalshSign (q ((x : V) + y) + a ((x : V) + y)) = _
    rw [binaryWalsh_quadratic_add, map_add,
      (binaryWalsh_mem_radical q x).mp x.property y, add_zero]
    rw [show q x + q y + (a x + a y) = (q x + a x) + (q y + a y) by ac_rfl,
      binaryWalshSign_add]

/-- The exact radical-compatibility condition for a nonzero Walsh coefficient. -/
def BinaryWalshCompatible (q : QuadraticMap (ZMod 2) V (ZMod 2))
    (a : V →+ ZMod 2) : Prop := ∀ x ∈ binaryWalshRadical q, q x = a x

theorem binaryWalshRadicalChar_eq_zero (q : QuadraticMap (ZMod 2) V (ZMod 2))
    (a : V →+ ZMod 2) : binaryWalshRadicalChar q a = 0 ↔ BinaryWalshCompatible q a := by
  constructor
  · intro h x hx
    have he := congrArg (fun f : AddChar (binaryWalshRadical q) ℤ => f ⟨x, hx⟩) h
    have hz : q x + a x = 0 := (binaryWalshSign_eq_one _).mp he
    exact eq_neg_of_add_eq_zero_left hz |>.trans (CharTwo.neg_eq _)
  · intro h
    ext x
    change binaryWalshSign (q x + a x) = 1
    rw [h x x.property, CharTwo.add_self_eq_zero, binaryWalshSign_zero]

end Atlas.Algebra
