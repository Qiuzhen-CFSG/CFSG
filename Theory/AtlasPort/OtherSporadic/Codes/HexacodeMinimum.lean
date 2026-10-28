/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeStructure

/-!
The constructed hexacode has minimum weight exactly four.
Pairwise weight bounds handle the seed coset, and nonzero pairs together with
evenness handle the twisting coset.

Source: `Atlas/Codes/HexacodeMinimum.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

def liftedPair (u : L) (r : Bit) : Fin 2 → K := phi u + fun _ => (r, 0)

theorem liftedPair_spin : ∀ r, hammingNorm (liftedPair spin r) = 2 := by decide
theorem liftedPair_cospin : ∀ r, hammingNorm (liftedPair cospin r) = 2 := by decide
theorem liftedPair_one : ∀ r, hammingNorm (liftedPair oneL r) = 1 := by decide
theorem liftedPair_zero : ∀ r, hammingNorm (liftedPair 0 r) = if r = 0 then 0 else 2 := by decide

theorem gluing_weight (x : TrioWord) (r : Fin 3 → Bit) :
    hammingNorm (phiWord x + equalPairs r) = ∑ i, hammingNorm (liftedPair (x i) (r i)) := by
  rw [hammingNorm_prod]
  rfl

theorem nonzero_seed_weight (x : TrioWord) (hx : x ∈ trio) (hx0 : x ≠ 0) (r : Fin 3 → Bit) :
    4 ≤ hammingNorm (phiWord x + equalPairs r) := by
  rw [trio_words] at hx
  simp only [trioWords, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (hx0 h)
  all_goals rw [gluing_weight]
  all_goals simp [Fin.sum_univ_succ, liftedPair_spin, liftedPair_cospin,
    liftedPair_one, liftedPair_zero] <;> omega

theorem pairParityEncoder_even (r : Fin 2 → Bit) : ∑ i, pairParityEncoder r i = 0 := by
  simp [pairParityEncoder, Fin.sum_univ_succ]

theorem equalPairs_weight (r : Fin 3 → Bit) : hammingNorm (equalPairs r) = 2 * hammingNorm r := by
  rw [hammingNorm_prod, hammingNorm_eq_sum r, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : ∀ s : Bit, hammingNorm (fun _ : Fin 2 => ((s, 0) : K)) = 2 * (if s = 0 then 0 else 1) := by decide
  exact h (r i)

theorem H0_minimum (w : HexWord) (hw : w ∈ H0) (hw0 : w ≠ 0) : 4 ≤ hammingNorm w := by
  obtain ⟨⟨x, r⟩, rfl⟩ := hw
  by_cases hx : trioEncoder x = 0
  · have he : h0Encoder (x, r) = equalPairs (pairParityEncoder r) := by
      simp [h0Encoder, hx, eEncoder]
    rw [he, equalPairs_weight]
    have hr : pairParityEncoder r ≠ 0 := by
      intro hr
      apply hw0
      rw [he, hr, map_zero]
    have hmin := positive_even_weight (pairParityEncoder r) hr
      ((even_weight_iff _).mpr (pairParityEncoder_even r))
    omega
  · exact nonzero_seed_weight (trioEncoder x) ⟨x, rfl⟩ hx (pairParityEncoder r)

theorem odd_pair_nonzero (t : (Fin 3 → Bit) × (Fin 2 → Bit)) (i : Fin 3) :
    (fun j : Fin 2 => (h0Encoder t + tau) (i, j)) ≠ 0 := by
  intro he
  have h0 := congrArg (fun v : Fin 2 → K => (v 0).2 + (v 1).2) he
  rcases t with ⟨x, r⟩
  fin_cases i <;>
    simp [h0Encoder, phiWord, phi, trioEncoder, eEncoder_apply, tau, b, c, a] at h0
  all_goals have hh : ∀ z : Bit, z + 1 + z ≠ 0 := by decide
  all_goals exact hh _ h0

theorem hexacode_minimum (w : HexWord) (hw : w ∈ hexacode) (hw0 : w ≠ 0) :
    4 ≤ hammingNorm w := by
  rcases (hexacode_cosets w).mp hw with h | ⟨v, ⟨t, rfl⟩, rfl⟩
  · exact H0_minimum w h hw0
  · have hl : 3 ≤ hammingNorm (h0Encoder t + tau) := by
      rw [hammingNorm_prod]
      calc
        3 = ∑ _ : Fin 3, 1 := by decide
        _ ≤ _ := Finset.sum_le_sum fun i _ => hammingNorm_pos_iff.mpr (odd_pair_nonzero t i)
    obtain ⟨k, hk⟩ := hexacode_even _ hw
    omega

theorem hexacode_minimum_exact :
    (∀ w ∈ hexacode, w ≠ 0 → 4 ≤ hammingNorm w) ∧
      ∃ w ∈ hexacode, hammingNorm w = 4 := by
  refine ⟨hexacode_minimum, hexGenerators 0, ?_, hexGenerators_weight 0⟩
  rw [← hexBasis_coe]
  exact (hexBasis 0).prop
end Atlas.Codes
