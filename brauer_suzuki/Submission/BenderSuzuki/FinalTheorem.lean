/-
Authors: Tianjiao Nie
-/

module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Parity
public import Submission.BenderSuzuki.PFchapter1section1.Basic
import Submission.BenderSuzuki.Suzuki

/-!
# Final Suzuki theorem interface

This module exposes the normal subgroup and power-of-two parameter supplied by
the Suzuki theorem, together with their principal properties.
-/

noncomputable section

namespace BenderSuzuki

open PFchapter1section1

universe u v

variable {G : Type u} {Ω : Type v}
variable [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
variable (H D Q : Subgroup G) (t : G)
variable (hA : HypothesisA G Ω H D Q t)

/-- The normal subgroup supplied by the Suzuki theorem. -/
public def suzukiKernel : Subgroup G := (suzuki H D Q t hA).choose

/-- The power-of-two parameter supplied by the Suzuki theorem. -/
public def suzukiKernelQ : ℕ :=
  (suzuki H D Q t hA).choose_spec.choose_spec.choose

/-- The subgroup supplied by the Suzuki theorem is normal. -/
public theorem suzukiKernel_normal : (suzukiKernel H D Q t hA).Normal := by
  exact (suzuki H D Q t hA).choose_spec.choose

/-- The quotient by the subgroup supplied by the Suzuki theorem has odd order. -/
public theorem suzukiKernel_quotient_odd :
    Odd (Nat.card (G ⧸ suzukiKernel H D Q t hA)) := by
  exact (suzuki H D Q t hA).choose_spec.choose_spec.choose_spec.1

/-- The parameter supplied by the Suzuki theorem is a power of two. -/
public theorem suzukiKernelQ_eq_two_pow :
    ∃ n : ℕ, suzukiKernelQ H D Q t hA = 2 ^ n := by
  exact (suzuki H D Q t hA).choose_spec.choose_spec.choose_spec.2.1

/-- The parameter supplied by the Suzuki theorem is greater than two. -/
public theorem suzukiKernelQ_gt_two : 2 < suzukiKernelQ H D Q t hA := by
  exact (suzuki H D Q t hA).choose_spec.choose_spec.choose_spec.2.2.1

end BenderSuzuki
