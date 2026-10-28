/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.ParityProjection

/-!
Weight counts in even Golay slices with fixed hexacode word.
The zero coordinates of that word reduce the weight formula to a parity-code
projection, whose fibers provide the counts.

Source: `Atlas/Codes/GolayEvenCounting.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators
open Finset

theorem hammingNorm_equiv {ι κ A : Type*} [Fintype ι] [Fintype κ] [Zero A] [DecidableEq A]
    (e : ι ≃ κ) (w : κ → A) : hammingNorm (fun i => w (e i)) = hammingNorm w := by
  rw [hammingNorm_eq_sum, hammingNorm_eq_sum]
  exact e.sum_comp (fun i => if w i = 0 then 0 else 1)

def zeroPositions (h : HexWord) : Finset (Fin 6) := univ.filter (fun i => h (hexIndexEquiv.symm i) = 0)

theorem zeroPositions_card (h : HexWord) : (zeroPositions h).card + hammingNorm h = 6 := by
  have he := card_filter_add_card_filter_not (s := univ) (fun i : Fin 6 => h (hexIndexEquiv.symm i) = 0)
  change (zeroPositions h).card + hammingNorm (fun i => h (hexIndexEquiv.symm i)) = 6 at he
  rwa [hammingNorm_equiv] at he

theorem zeroPositions_embedding (h : HexWord) (hh : hammingNorm h = 4) :
    ∃ e : Fin 2 ↪ Fin 6, ∀ i, h (hexIndexEquiv.symm i) = 0 ↔ ∃ j, e j = i := by
  have hc : (zeroPositions h).card = 2 := by have := zeroPositions_card h; omega
  let E := equivFinOfCardEq hc
  let e : Fin 2 ↪ Fin 6 := ⟨fun j => (E.symm j).val,
    fun _ _ he => E.symm.injective (Subtype.ext he)⟩
  refine ⟨e, fun i => ?_⟩
  constructor
  · intro hi
    have him : i ∈ zeroPositions h := by simp [zeroPositions, hi]
    refine ⟨E ⟨i,him⟩, ?_⟩
    change (E.symm (E ⟨i,him⟩)).val = i
    simp
  · rintro ⟨j,rfl⟩
    have hp := (E.symm j).prop
    exact (mem_filter.mp hp).2

theorem c0Encoder_weight_formula (h : hexacode) (r : P6) :
    hammingNorm (c0Encoder (h,r)) = 2 * hammingNorm h.val +
      4 * #{i : Fin 6 | h.val (hexIndexEquiv.symm i) = 0 ∧ r.val i ≠ 0} := by
  rw [hammingNorm_prod]
  have he (i : HexIndex) : hammingNorm (fun k => c0Encoder (h,r) (i,k)) =
      2 * (if h.val i = 0 then 0 else 1) +
        4 * (if h.val i = 0 ∧ r.val (hexIndexEquiv i) ≠ 0 then 1 else 0) := by
    change hammingNorm (j (h.val i) + fun _ => r.val (hexIndexEquiv i)) = _
    rw [complemented_j_weight]
    split_ifs <;> simp_all
  simp only [he, sum_add_distrib, ← mul_sum, ← hammingNorm_eq_sum]
  have hs := hexIndexEquiv.sum_comp (fun i : Fin 6 =>
    if h.val (hexIndexEquiv.symm i) = 0 ∧ r.val i ≠ 0 then 1 else 0 : Fin 6 → ℕ)
  simp only [Equiv.symm_apply_apply] at hs
  rw [hs, ← card_filter]

theorem c0_weight_four (h : hexacode) (hh : hammingNorm h.val = 4)
    (e : Fin 2 ↪ Fin 6) (he : ∀ i, h.val (hexIndexEquiv.symm i) = 0 ↔ ∃ j, e j = i)
    (r : P6) : hammingNorm (c0Encoder (h,r)) = 8 + 4 * hammingNorm (parityProjection e r) := by
  rw [c0Encoder_weight_formula, hh]
  have hs : (univ.filter (fun i : Fin 6 => h.val (hexIndexEquiv.symm i) = 0 ∧ r.val i ≠ 0)) =
      (univ.filter (fun j : Fin 2 => r.val (e j) ≠ 0)).image e := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_image, he]
    constructor
    · rintro ⟨⟨j,rfl⟩,hj⟩
      exact ⟨j,hj,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      exact ⟨⟨j,rfl⟩,hj⟩
  rw [hs, card_image_of_injective _ e.injective]
  rfl

theorem c0_weight_four_count (h : hexacode) (hh : hammingNorm h.val = 4) (m : ℕ) :
    Nat.card {r : P6 // hammingNorm (c0Encoder (h,r)) = 8 + 4*m} = 8 * (2 : ℕ).choose m := by
  obtain ⟨e,he⟩ := zeroPositions_embedding h.val hh
  let E : {r : P6 // hammingNorm (c0Encoder (h,r)) = 8 + 4*m} ≃
      {r : P6 // hammingNorm (parityProjection e r) = m} :=
    Equiv.subtypeEquivRight (fun r => by rw [c0_weight_four h hh e he r]; omega)
  rw [Nat.card_congr E, parityProjection_weight_count]

theorem c0_weight_six (h : hexacode) (hh : hammingNorm h.val = 6) (r : P6) :
    hammingNorm (c0Encoder (h,r)) = 12 := by
  have hz : zeroPositions h.val = ∅ := card_eq_zero.mp (by have := zeroPositions_card h.val; omega)
  have hi (i : Fin 6) : h.val (hexIndexEquiv.symm i) ≠ 0 := by
    intro he
    have hm : i ∈ zeroPositions h.val := by simp [zeroPositions, he]
    rw [hz] at hm
    simp at hm
  rw [c0Encoder_weight_formula, hh]
  simp [hi]

theorem c0_weight_zero_count (m : ℕ) :
    Nat.card {r : P6 // hammingNorm (c0Encoder (0,r)) = 4*m} =
      if Even m then (6 : ℕ).choose m else 0 := by
  let E : {r : P6 // hammingNorm (c0Encoder (0,r)) = 4*m} ≃
      {r : P6 // hammingNorm r.val = m} :=
    Equiv.subtypeEquivRight (fun r => by simp only [c0Encoder, Submodule.coe_zero,
      map_zero, zero_add, LinearMap.coe_mk, AddHom.coe_mk, rho_weight]; omega)
  rw [Nat.card_congr E, parity_weight_count]

end Atlas.Codes
