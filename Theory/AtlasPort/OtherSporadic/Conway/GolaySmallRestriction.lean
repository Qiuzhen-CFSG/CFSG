/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/GolaySmallRestriction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.GolayTwoCoordinateFiber
/-!
Golay coordinate restrictions and signed-support transport in the Leech lattice.
The proofs retain the explicit code maps and coordinate identities used by the stabilizer geometry.

Source: Gerald Höhn, `Atlas/Conway/GolaySmallRestriction.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def golayRestriction (T : Finset Omega) : golay →ₗ[Bit] (T → Bit) where
  toFun c i := c.val i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def codeZeroExtend (T : Finset Omega) (w : T → Bit) : BinaryWord :=
  fun i => if hi : i ∈ T then w ⟨i,hi⟩ else 0

theorem codeZeroExtend_apply (T : Finset Omega) (w : T → Bit) (i : T) :
    codeZeroExtend T w i.val = w i := by simp [codeZeroExtend]

theorem codeZeroExtend_dot (T : Finset Omega) (w : T → Bit) (c : BinaryWord) :
    binaryDot c (codeZeroExtend T w) = binaryDot (fun i : T => c i) w := by
  have hs : (∑ i ∈ T, c i * codeZeroExtend T w i) =
      ∑ i, c i * codeZeroExtend T w i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [codeZeroExtend,hi]
  rw [binaryDot_apply,← hs,← Finset.sum_coe_sort]
  simp only [codeZeroExtend_apply,binaryDot_apply]

theorem codeZeroExtend_weight_le (T : Finset Omega) (w : T → Bit) :
    hammingNorm (codeZeroExtend T w) ≤ T.card := by
  apply Finset.card_le_card
  intro i hi
  have hh := (Finset.mem_filter.mp hi).2
  by_contra hn
  exact hh (by simp [codeZeroExtend,hn])

theorem golay_restriction_orthogonal (T : Finset Omega) (w : T → Bit) :
    w ∈ binaryDot.orthogonal (golayRestriction T).range ↔ codeZeroExtend T w ∈ golay := by
  conv_rhs => rw [golay_selfDual]
  constructor
  · intro hw c hc
    have he := hw (golayRestriction T ⟨c,hc⟩) ⟨⟨c,hc⟩,rfl⟩
    exact (codeZeroExtend_dot T w c).trans he
  · intro hw x hx
    obtain ⟨c,rfl⟩ := hx
    exact (codeZeroExtend_dot T w c.val).symm.trans (hw c.val c.prop)

theorem golay_small_restriction_surjective (T : Finset Omega) (hT : T.card < 8) :
    Function.Surjective (golayRestriction T) := by
  have hz : binaryDot.orthogonal (golayRestriction T).range = ⊥ := by
    apply le_antisymm _ bot_le
    intro w hw
    have hc := (golay_restriction_orthogonal T w).mp hw
    have he : codeZeroExtend T w = 0 := by
      by_contra hn
      have hmin := golay_minimum _ hc hn
      have hle := codeZeroExtend_weight_le T w
      omega
    change w = 0
    funext i
    have hh := congrFun he i.val
    simpa only [codeZeroExtend_apply,Pi.zero_apply] using hh
  have hr : (binaryDot (ι := T)).IsRefl := by
    intro x y h
    exact (binaryDot_symmetric y x).trans h
  have he := binaryDot.orthogonal_orthogonal binaryDot_nondegenerate hr (golayRestriction T).range
  rw [hz,LinearMap.BilinForm.orthogonal_bot] at he
  exact LinearMap.range_eq_top.mp he.symm

end Atlas.Conway
