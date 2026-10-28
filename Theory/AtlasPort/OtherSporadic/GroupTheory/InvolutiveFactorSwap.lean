/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/InvolutiveFactorSwap.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Fixed points of an involutive factor swap

A product equivalence that interchanges two factors identifies the fixed
points with either factor and determines the ambient cardinality.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/InvolutiveFactorSwap.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and public imports.
-/

@[expose] public section

namespace Atlas.GroupTheory

/-- If an involution interchanges two identified direct factors, its fixed
points are exactly the diagonal factor. This is a statement about actual maps
and an actual product equivalence, not an inference from orders. -/
def factorSwapFixedEquiv {K N : Type*} (e : K ≃ N × N) (a : K → K)
    (ha : ∀ k, e (a k) = ((e k).2, (e k).1)) :
    {k : K // a k = k} ≃ N where
  toFun k := (e k.val).1
  invFun n := ⟨e.symm (n,n), by
    apply e.injective
    rw [ha]
    simp⟩
  left_inv k := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    have h := congrArg e k.property
    rw [ha] at h
    exact Prod.ext rfl (congrArg Prod.fst h).symm
  right_inv n := by simp

/-- A factor-swapping involution has as many fixed points as either factor. -/
theorem card_fixed_factorSwap {K N : Type*} (e : K ≃ N × N) (a : K → K)
    (ha : ∀ k, e (a k) = ((e k).2, (e k).1)) :
    Nat.card {k : K // a k = k} = Nat.card N :=
  Nat.card_congr (factorSwapFixedEquiv e a ha)

/-- The ambient order is the square of the fixed-point order whenever an
actual product decomposition carries the involution to factor interchange. -/
theorem card_eq_sq_fixed_factorSwap {K N : Type*} (e : K ≃ N × N) (a : K → K)
    (ha : ∀ k, e (a k) = ((e k).2, (e k).1)) :
    Nat.card K = (Nat.card {k : K // a k = k}) ^ 2 := by
  rw [card_fixed_factorSwap e a ha, Nat.card_congr e, Nat.card_prod, pow_two]

end Atlas.GroupTheory
