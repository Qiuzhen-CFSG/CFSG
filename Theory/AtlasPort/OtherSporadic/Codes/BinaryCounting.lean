/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.GolayBasis
public import Mathlib.Data.Fintype.Powerset

/-!
Weight counts for binary words and parity fibers.
Support gives an equivalence with subsets; parity restriction and translation
reduce the counts to binomial coefficients.

Source: `Atlas/Codes/BinaryCounting.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators
open Finset

noncomputable def binarySupportEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] : (ι → Bit) ≃ Finset ι where
  toFun := support
  invFun s i := if i ∈ s then 1 else 0
  left_inv := by
    classical
    intro w
    funext i
    rcases bit_cases (w i) with h | h <;> simp [support, h]
  right_inv := by
    classical
    intro s
    ext i
    simp [support]

theorem binary_weight_count (n k : ℕ) :
    Nat.card {w : Fin n → Bit // hammingNorm w = k} = n.choose k := by
  classical
  let e : {w : Fin n → Bit // hammingNorm w = k} ≃ {s : Finset (Fin n) // s.card = k} :=
    Equiv.subtypeEquiv binarySupportEquiv (fun w => Iff.rfl)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]

noncomputable def parityFiberEquiv (n : ℕ) : parityCode n ≃ {w : Fin (n+1) → Bit // ∑ i, w i = 0} where
  toFun w := ⟨w.val, (parityCode_mem n w.val).mp w.prop⟩
  invFun w := ⟨w.val, (parityCode_mem n w.val).mpr w.prop⟩
  left_inv := by intro w; rfl
  right_inv := by intro w; rfl

theorem parity_weight_count (n k : ℕ) :
    Nat.card {w : parityCode n // hammingNorm w.val = k} =
      if Even k then (n+1).choose k else 0 := by
  classical
  by_cases hk : Even k
  · let e : {w : parityCode n // hammingNorm w.val = k} ≃
        {w : Fin (n+1) → Bit // hammingNorm w = k} := {
      toFun := fun w => ⟨w.val.val, w.prop⟩
      invFun := fun w => ⟨⟨w.val, (parityCode_mem n w.val).mpr
        ((even_weight_iff w.val).mp (by rw [w.prop]; exact hk))⟩, w.prop⟩
      left_inv := by intro w; rfl
      right_inv := by intro w; rfl }
    rw [Nat.card_congr e, binary_weight_count, if_pos hk]
  · have hi : IsEmpty {w : parityCode n // hammingNorm w.val = k} := ⟨by
      intro w
      apply hk
      rw [← w.prop]
      exact (even_weight_iff w.val.val).mpr ((parityCode_mem n w.val.val).mp w.val.prop)⟩
    simp [Nat.card_eq_fintype_card, hk]

/-- Translation gives the parity coset, with its values fixed explicitly. -/
noncomputable def oddParityTranslation (n : ℕ) (b : Fin (n+1) → Bit) (hb : ∑ i, b i = 1) :
    parityCode n ≃ {s : Fin (n+1) → Bit // ∑ i, s i = 1} where
  toFun r := ⟨r.val + b, by
    rw [show (∑ i, (r.val + b) i) = (∑ i, r.val i) + ∑ i, b i by simp [sum_add_distrib]]
    rw [(parityCode_mem n r.val).mp r.prop, hb, zero_add]⟩
  invFun s := ⟨s.val + b, (parityCode_mem n _).mpr (by
    simp only [Pi.add_apply, sum_add_distrib, s.prop, hb, bit_self_add])⟩
  left_inv := by intro r; apply Subtype.ext; funext i; simp [add_assoc]
  right_inv := by intro s; apply Subtype.ext; funext i; simp [add_assoc]

theorem odd_parity_weight_count (n k : ℕ) :
    Nat.card {w : {s : Fin n → Bit // ∑ i, s i = 1} // hammingNorm w.val = k} =
      if (k : Bit) = 1 then n.choose k else 0 := by
  classical
  by_cases hk : (k : Bit) = 1
  · let e : {w : {s : Fin n → Bit // ∑ i, s i = 1} // hammingNorm w.val = k} ≃
        {w : Fin n → Bit // hammingNorm w = k} := {
      toFun := fun w => ⟨w.val.val, w.prop⟩
      invFun := fun w => ⟨⟨w.val, by rw [bit_sum_eq_weight, w.prop, hk]⟩, w.prop⟩
      left_inv := by intro w; rfl
      right_inv := by intro w; rfl }
    rw [Nat.card_congr e, binary_weight_count, if_pos hk]
  · have hi : IsEmpty {w : {s : Fin n → Bit // ∑ i, s i = 1} // hammingNorm w.val = k} := ⟨by
      intro w
      apply hk
      rw [← w.prop, ← bit_sum_eq_weight]
      exact w.val.prop⟩
    simp [Nat.card_eq_fintype_card, hk]

end Atlas.Codes
