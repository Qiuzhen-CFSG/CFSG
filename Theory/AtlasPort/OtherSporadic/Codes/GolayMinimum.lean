/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.GolayDuality

/-!
The constructed binary Golay code has minimum distance exactly eight.
Hexacode weights bound the even coset, while block parity and double evenness
bound the odd coset; the twist attains the bound.

Source: `Atlas/Codes/GolayMinimum.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

theorem complemented_j_weight : ∀ (u : K) (r : Bit),
    hammingNorm (j u + fun _ => r) =
      if u = 0 then 4 * (if r = 0 then 0 else 1) else 2 := by decide

theorem c0Encoder_weight_bound (h : hexacode) (r : P6) :
    2 * hammingNorm h.val ≤ hammingNorm (c0Encoder (h,r)) := by
  rw [hammingNorm_eq_sum h.val, Finset.mul_sum, hammingNorm_prod]
  apply Finset.sum_le_sum
  intro i _
  change 2 * (if h.val i = 0 then 0 else 1) ≤
    hammingNorm (j (h.val i) + fun _ => r.val (hexIndexEquiv i))
  rw [complemented_j_weight]
  split_ifs <;> omega

theorem C0_minimum (w : BinaryWord) (hw : w ∈ C0) (hw0 : w ≠ 0) : 8 ≤ hammingNorm w := by
  obtain ⟨⟨h,r⟩,rfl⟩ := hw
  by_cases hh : h.val = 0
  · have he : c0Encoder (h,r) = rho r.val := by simp [c0Encoder, hh]
    have hr : r.val ≠ 0 := by
      intro hr
      apply hw0
      rw [he, hr, map_zero]
    have hp := positive_even_weight r.val hr
      ((even_weight_iff r.val).mpr ((parityCode_mem 5 r.val).mp r.prop))
    rw [he, rho_weight]
    omega
  · have hm := hexacode_minimum h.val h.prop hh
    have hb := c0Encoder_weight_bound h r
    omega

theorem golay_minimum (w : BinaryWord) (hw : w ∈ golay) (hw0 : w ≠ 0) : 8 ≤ hammingNorm w := by
  rcases (golay_cosets w).mp hw with h | ⟨v,⟨⟨h,r⟩,rfl⟩,rfl⟩
  · exact C0_minimum w h hw0
  · have hl : 6 ≤ hammingNorm (c0Encoder (h,r) + eta) := by
      rw [hammingNorm_prod]
      calc
        6 = ∑ _ : HexIndex, 1 := by decide
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i _
          apply hammingNorm_pos_iff.mpr
          intro he
          have hp := golayEncoder_blockParity h r 1 i
          simp only [golayEncoder, LinearMap.coe_mk, AddHom.coe_mk, one_smul] at hp
          have hz : blockParity (c0Encoder (h,r) + eta) i = 0 := by
            unfold blockParity
            change (∑ k, (fun k => (c0Encoder (h,r) + eta) (i,k)) k) = 0
            rw [he]
            simp
          rw [hz] at hp
          exact zero_ne_one hp
    have hd := golay_doublyEven _ hw
    omega

theorem eta_mem_golay : eta ∈ golay := by
  exact ⟨(0,0,1), by simp [golayEncoder, c0Encoder]⟩

theorem golay_minimum_exact :
    (∀ w ∈ golay, w ≠ 0 → 8 ≤ hammingNorm w) ∧
      ∃ w ∈ golay, hammingNorm w = 8 :=
  ⟨golay_minimum, eta, eta_mem_golay, eta_weight⟩

theorem golay_distance (u v : golay) (huv : u ≠ v) : 8 ≤ hammingDist u.val v.val := by
  rw [hammingDist_eq_hammingNorm]
  apply golay_minimum _ (golay.add_mem (golay.neg_mem u.prop) v.prop)
  intro he
  apply huv
  exact Subtype.ext (neg_add_eq_zero.mp he)

end Atlas.Codes
