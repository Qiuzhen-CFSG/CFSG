/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.GolayEvenCounting
public import Theory.AtlasPort.OtherSporadic.Codes.GolayOddCounting

/-!
The middle weight counts of the binary Golay code and its two cosets.
Sum the fixed-hexacode slices using the hexacode distribution, then combine
the disjoint even and odd cosets.

Source: `Atlas/Codes/GolayCounts.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators
open Finset
noncomputable instance : Fintype C0 := Fintype.ofFinite C0
noncomputable instance : Fintype golay := Fintype.ofFinite golay

def middleWeights : Fin 3 → ℕ := ![8,12,16]
noncomputable def evenCosetCount (k : ℕ) := Nat.card {w : C0 // hammingNorm w.val = k}
noncomputable def oddCosetCount (k : ℕ) := Nat.card {w : C0 // hammingNorm (w.val + eta) = k}
noncomputable def golayWeightCount (k : ℕ) := Nat.card {w : golay // hammingNorm w.val = k}

theorem card_subtype_prod_sum {A B : Type*} [Fintype A] [Fintype B] (p : A × B → Prop) :
    Nat.card {x : A × B // p x} = ∑ a : A, Nat.card {b : B // p (a,b)} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, card_filter, Fintype.sum_prod_type]

theorem evenCosetCount_sum (k : ℕ) : evenCosetCount k =
    ∑ h : hexacode, Nat.card {r : P6 // hammingNorm (c0Encoder (h,r)) = k} := by
  let e := Equiv.subtypeEquivOfSubtype c0Equiv.toEquiv
    (p := fun w : C0 => hammingNorm w.val = k)
  rw [evenCosetCount, ← Nat.card_congr e]
  exact card_subtype_prod_sum _

theorem oddCosetCount_sum (k : ℕ) : oddCosetCount k =
    ∑ h : hexacode, Nat.card {r : P6 // hammingNorm (c0Encoder (h,r) + eta) = k} := by
  let e := Equiv.subtypeEquivOfSubtype c0Equiv.toEquiv
    (p := fun w : C0 => hammingNorm (w.val + eta) = k)
  rw [oddCosetCount, ← Nat.card_congr e]
  exact card_subtype_prod_sum _

theorem even_slice_zero (i : Fin 3) :
    Nat.card {r : P6 // hammingNorm (c0Encoder (0,r)) = middleWeights i} = ![15,0,15] i := by
  have h2 := c0_weight_zero_count 2
  have h3 := c0_weight_zero_count 3
  have h4 := c0_weight_zero_count 4
  norm_num [Nat.choose] at h2 h3 h4
  fin_cases i
  · simpa [Nat.card_eq_fintype_card, middleWeights] using h2
  · simpa [Nat.card_eq_fintype_card, middleWeights] using h3
  · simpa [Nat.card_eq_fintype_card, middleWeights] using h4

theorem even_slice_four (h : hexacode) (hh : hammingNorm h.val = 4) (i : Fin 3) :
    Nat.card {r : P6 // hammingNorm (c0Encoder (h,r)) = middleWeights i} = ![8,16,8] i := by
  have h0 := c0_weight_four_count h hh 0
  have h1 := c0_weight_four_count h hh 1
  have h2 := c0_weight_four_count h hh 2
  norm_num [Nat.choose] at h0 h1 h2
  fin_cases i
  · simpa [Nat.card_eq_fintype_card, middleWeights] using h0
  · simpa [Nat.card_eq_fintype_card, middleWeights] using h1
  · simpa [Nat.card_eq_fintype_card, middleWeights] using h2

theorem even_slice_six (h : hexacode) (hh : hammingNorm h.val = 6) (i : Fin 3) :
    Nat.card {r : P6 // hammingNorm (c0Encoder (h,r)) = middleWeights i} = ![0,32,0] i := by
  classical
  have hc : Fintype.card P6 = 32 := by simpa [Nat.card_eq_fintype_card] using parityCode_card 5
  fin_cases i <;> simp [Nat.card_eq_fintype_card, Fintype.card_subtype, c0_weight_six h hh,
    middleWeights, hc]

theorem even_middle_counts (i : Fin 3) : evenCosetCount (middleWeights i) = ![375,1296,375] i := by
  rw [evenCosetCount_sum]
  have he (h : hexacode) :
      Nat.card {r : P6 // hammingNorm (c0Encoder (h,r)) = middleWeights i} =
        ![15,0,15] i * (if hammingNorm h.val = 0 then 1 else 0) +
        ![8,16,8] i * (if hammingNorm h.val = 4 then 1 else 0) +
        ![0,32,0] i * (if hammingNorm h.val = 6 then 1 else 0) := by
    rcases hex_weights h with hh | hh | hh
    · have h0 : h = 0 := Subtype.ext (hammingNorm_eq_zero.mp hh)
      subst h
      simpa using even_slice_zero i
    · simpa [hh] using even_slice_four h hh i
    · simpa [hh] using even_slice_six h hh i
  simp only [he, sum_add_distrib, ← mul_sum, ← card_filter]
  change ![15,0,15] i * hexWeightCount 0 + ![8,16,8] i * hexWeightCount 4 +
    ![0,32,0] i * hexWeightCount 6 = _
  rw [hexacode_weight_distribution, hexacode_weight_distribution, hexacode_weight_distribution]
  fin_cases i <;> norm_num

theorem odd_middle_counts (i : Fin 3) : oddCosetCount (middleWeights i) = ![384,1280,384] i := by
  rw [oddCosetCount_sum]
  have he (h : hexacode) :
      Nat.card {r : P6 // hammingNorm (c0Encoder (h,r) + eta) = middleWeights i} = ![6,20,6] i := by
    have hh := odd_word_counts h
    fin_cases i
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
  simp only [he, sum_const, card_univ, smul_eq_mul]
  have hc : Fintype.card hexacode = 64 := by simpa [Nat.card_eq_fintype_card] using hexacode_card
  rw [hc]
  fin_cases i <;> norm_num

theorem golayWeightCount_cosets (k : ℕ) : golayWeightCount k = evenCosetCount k + oddCosetCount k := by
  classical
  let e := Equiv.subtypeEquivOfSubtype golayEquiv.toEquiv
    (p := fun w : golay => hammingNorm w.val = k)
  rw [golayWeightCount, ← Nat.card_congr e, card_subtype_prod_sum]
  simp only [card_subtype_prod_sum]
  have hu : (univ : Finset Bit) = {0,1} := by decide
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, card_filter, hu,
    sum_insert, mem_singleton, zero_ne_one, not_false_eq_true, sum_singleton,
    ]
  have he0 (h : hexacode) (r : P6) :
      (golayEquiv.toEquiv (h,r,0)).val = c0Encoder (h,r) := by
    have hg := golayEquiv_apply h r 0
    simp only [zero_smul, add_zero] at hg
    exact hg
  have he1 (h : hexacode) (r : P6) :
      (golayEquiv.toEquiv (h,r,1)).val = c0Encoder (h,r) + eta := by
    have hg := golayEquiv_apply h r 1
    simp only [one_smul] at hg
    exact hg
  simp only [he0, he1]
  simp only [sum_add_distrib]
  rw [evenCosetCount_sum, oddCosetCount_sum]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, card_filter]

theorem golay_middle_counts (i : Fin 3) : golayWeightCount (middleWeights i) = ![759,2576,759] i := by
  rw [golayWeightCount_cosets, even_middle_counts, odd_middle_counts]
  fin_cases i <;> norm_num
end Atlas.Codes
