/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Fischer/ParkerFactorSet.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Tactic

/-!
# Parker factor sets and multiplication

The explicit bilinear and trilinear formula gives the factor-set defect.
Additive coordinate calculations prove the unit and division identities; no
associative multiplication is asserted.

Source: Gerald Höhn, ATLAS, `Atlas/Fischer/ParkerFactorSet.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed because downstream coordinate proofs unfold them.
-/

@[expose] public section


/-! Algebraic identities for the ordered-basis Parker factor set.
The trilinear form and bilinear correction are explicit input data here;
their code-theoretic specialization is a separate obligation. -/

namespace Atlas.Fischer

abbrev ParkerBit := ZMod 2

variable {V : Type*} [AddCommGroup V] [Module ParkerBit V]

def parkerFactorSet
    (θ : V →ₗ[ParkerBit] V →ₗ[ParkerBit] V →ₗ[ParkerBit] ParkerBit)
    (β : V →ₗ[ParkerBit] V →ₗ[ParkerBit] ParkerBit) (a b : V) : ParkerBit :=
  θ a b b + β a b

@[simp] theorem parkerFactorSet_zero_left
    (θ : V →ₗ[ParkerBit] V →ₗ[ParkerBit] V →ₗ[ParkerBit] ParkerBit)
    (β : V →ₗ[ParkerBit] V →ₗ[ParkerBit] ParkerBit) (a : V) :
    parkerFactorSet θ β 0 a = 0 := by simp [parkerFactorSet]

@[simp] theorem parkerFactorSet_zero_right
    (θ : V →ₗ[ParkerBit] V →ₗ[ParkerBit] V →ₗ[ParkerBit] ParkerBit)
    (β : V →ₗ[ParkerBit] V →ₗ[ParkerBit] ParkerBit) (a : V) :
    parkerFactorSet θ β a 0 = 0 := by simp [parkerFactorSet]

theorem parkerFactorSet_defect
    (θ : V →ₗ[ParkerBit] V →ₗ[ParkerBit] V →ₗ[ParkerBit] ParkerBit)
    (β : V →ₗ[ParkerBit] V →ₗ[ParkerBit] ParkerBit) (a b c : V) :
    parkerFactorSet θ β a b + parkerFactorSet θ β (a + b) c +
      parkerFactorSet θ β b c + parkerFactorSet θ β a (b + c) =
        θ a b c + θ a c b := by
  simp only [parkerFactorSet, map_add, LinearMap.add_apply]
  ring_nf
  simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, add_zero, zero_add]

/-- Additive sign coordinates; no associative multiplication is asserted. -/
def parkerMultiply (f : V → V → ParkerBit) (x y : V × ParkerBit) : V × ParkerBit :=
  (x.1 + y.1, x.2 + y.2 + f x.1 y.1)

-- Retain the upstream module parameter on the multiplication identities.
set_option linter.unusedSectionVars false

theorem parkerMultiply_one_left (f : V → V → ParkerBit)
    (hf : ∀ a, f 0 a = 0) (x : V × ParkerBit) :
    parkerMultiply f (0, 0) x = x := by
  simp [parkerMultiply, hf]

theorem parkerMultiply_one_right (f : V → V → ParkerBit)
    (hf : ∀ a, f a 0 = 0) (x : V × ParkerBit) :
    parkerMultiply f x (0, 0) = x := by
  simp [parkerMultiply, hf]

theorem parkerMultiply_square (f : V → V → ParkerBit) (x : V × ParkerBit) :
    parkerMultiply f x x = (x.1 + x.1, f x.1 x.1) := by
  simp only [parkerMultiply, Prod.mk.injEq, true_and]
  ring_nf
  simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, zero_add]

def parkerLeftDivide (f : V → V → ParkerBit) (x y : V × ParkerBit) : V × ParkerBit :=
  (y.1 - x.1, y.2 - x.2 - f x.1 (y.1 - x.1))

def parkerRightDivide (f : V → V → ParkerBit) (x y : V × ParkerBit) : V × ParkerBit :=
  (x.1 - y.1, x.2 - y.2 - f (x.1 - y.1) y.1)

theorem parkerMultiply_leftDivide (f : V → V → ParkerBit) (x y : V × ParkerBit) :
    parkerMultiply f x (parkerLeftDivide f x y) = y := by
  apply Prod.ext <;> simp only [parkerMultiply, parkerLeftDivide] <;> abel

theorem parkerLeftDivide_multiply (f : V → V → ParkerBit) (x y : V × ParkerBit) :
    parkerLeftDivide f x (parkerMultiply f x y) = y := by
  apply Prod.ext
  · simp [parkerMultiply, parkerLeftDivide]
  · simp only [parkerMultiply, parkerLeftDivide, add_sub_cancel_left]
    abel

theorem parkerMultiply_rightDivide (f : V → V → ParkerBit) (x y : V × ParkerBit) :
    parkerMultiply f (parkerRightDivide f x y) y = x := by
  apply Prod.ext <;> simp only [parkerMultiply, parkerRightDivide] <;> abel

theorem parkerRightDivide_multiply (f : V → V → ParkerBit) (x y : V × ParkerBit) :
    parkerRightDivide f (parkerMultiply f x y) y = x := by
  apply Prod.ext
  · simp [parkerMultiply, parkerRightDivide]
  · simp only [parkerMultiply, parkerRightDivide, add_sub_cancel_right]
    abel

end Atlas.Fischer
