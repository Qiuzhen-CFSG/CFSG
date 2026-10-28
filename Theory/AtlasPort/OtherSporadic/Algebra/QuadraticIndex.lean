/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/QuadraticIndex.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.Tactic

/-!
# Lattice indices from a quadratic scalar relation

The determinant index formula and a square-root scalar relation compute the cardinality of an integral lattice quotient.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/QuadraticIndex.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Algebra

/-- The determinant index formula for an injective integral endomorphism. -/
theorem card_quotient_range_eq_natAbs_det
    {M : Type*} [AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M]
    (f : Module.End ℤ M) (hf : Function.Injective f) :
    Nat.card (M ⧸ f.range) = (LinearMap.det f).natAbs := by
  have h := Submodule.natAbs_det_equiv f.range (LinearEquiv.ofInjective f hf)
  exact h.symm

/-- A square-root scalar relation computes the lattice quotient index. -/
theorem card_quotient_range_of_square_neg
    {M : Type*} [AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M]
    (f : Module.End ℤ M) (hf : Function.Injective f)
    (p r : ℕ) (hdim : Module.finrank ℤ M = 2*r)
    (hs : f*f = (-(p : ℤ)) • (1 : Module.End ℤ M)) :
    Nat.card (M ⧸ f.range) = p^r := by
  rw [card_quotient_range_eq_natAbs_det f hf]
  have hd := congrArg LinearMap.det hs
  simp only [map_mul, LinearMap.det_smul, map_one, mul_one, hdim] at hd
  have hn := congrArg Int.natAbs hd
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast] at hn
  have hsq : (LinearMap.det f).natAbs ^ 2 = (p^r)^2 := by
    rw [pow_two, ← pow_mul]
    simpa [Nat.mul_comm] using hn
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) hsq

end Atlas.Algebra
