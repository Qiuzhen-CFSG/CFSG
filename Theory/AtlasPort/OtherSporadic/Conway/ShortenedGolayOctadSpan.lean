/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/ShortenedGolayOctadSpan.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalLineSigns
public import Theory.AtlasPort.OtherSporadic.Codes.GolayBasis

/-!
The shortened Golay code is spanned by octads avoiding a marked pair.
The proof projects the Golay basis and expresses each projected vector using explicit octad words.

Source: Gerald Höhn, `Atlas/Conway/ShortenedGolayOctadSpan.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

def markedShortOctads : Set golay := {c | c.val ((0,0),0) = 0 ∧
  c.val ((0,0),1) = 0 ∧ hammingNorm c.val = 8}

def markedShortSpan : Submodule Bit golay := Submodule.span Bit markedShortOctads

def markedShortProjection : golay →ₗ[Bit] golay where
  toFun c := c - c.val ((0,0),0) • golayBasis 11 - c.val ((0,0),1) • golayBasis 0
  map_add' c d := by simp [add_smul]; abel
  map_smul' r c := by simp [smul_sub,smul_smul]

def shortAdjustment (k : Fin 12) : golay :=
  if k = 6 ∨ k = 9 then golayBasis 2 else if k = 7 then golayBasis 4
  else if k = 8 then golayBasis 3 + golayBasis 4
  else if k = 10 then golayBasis 6 + golayBasis 7 else 0

theorem shortAdjustment_mem (k : Fin 12) : shortAdjustment k ∈ markedShortSpan := by
  by_cases h : k = 6 ∨ k = 9 ∨ k = 7 ∨ k = 8 ∨ k = 10
  · apply Submodule.subset_span
    change (shortAdjustment k).val ((0,0),0) = 0 ∧
      (shortAdjustment k).val ((0,0),1) = 0 ∧ hammingNorm (shortAdjustment k).val = 8
    fin_cases k <;> simp_all [shortAdjustment]
    all_goals simp only [golayBasis_coe]
    all_goals decide +kernel
  · have he : shortAdjustment k = 0 := by simp [shortAdjustment]; aesop
    rw [he]
    exact Submodule.zero_mem _

theorem short_corrected_basis_octad (k : Fin 12) (hk0 : k ≠ 0) (hk11 : k ≠ 11) :
    markedShortProjection (golayBasis k) + shortAdjustment k ∈ markedShortOctads := by
  change ((markedShortProjection (golayBasis k) + shortAdjustment k).val ((0,0),0) = 0 ∧
    (markedShortProjection (golayBasis k) + shortAdjustment k).val ((0,0),1) = 0 ∧
    hammingNorm (markedShortProjection (golayBasis k) + shortAdjustment k).val = 8)
  fin_cases k <;> try contradiction
  all_goals simp [markedShortProjection,LinearMap.coe_mk,AddHom.coe_mk,
    shortAdjustment,Submodule.coe_add,golayBasis_coe]
  all_goals decide +kernel

theorem short_projected_basis_mem (k : Fin 12) : markedShortProjection (golayBasis k) ∈ markedShortSpan := by
  by_cases h0 : k = 0
  · subst k
    have he : markedShortProjection (golayBasis 0) = 0 := by
      apply Subtype.ext
      simp only [markedShortProjection,LinearMap.coe_mk,AddHom.coe_mk,
        Submodule.coe_sub,Submodule.coe_smul,golayBasis_coe]
      decide +kernel
    rw [he]
    exact Submodule.zero_mem _
  by_cases h11 : k = 11
  · subst k
    have he : markedShortProjection (golayBasis 11) = 0 := by
      apply Subtype.ext
      simp only [markedShortProjection,LinearMap.coe_mk,AddHom.coe_mk,
        Submodule.coe_sub,Submodule.coe_smul,golayBasis_coe]
      decide +kernel
    rw [he]
    exact Submodule.zero_mem _
  have ha := shortAdjustment_mem k
  have hc : markedShortProjection (golayBasis k) + shortAdjustment k ∈ markedShortSpan :=
    Submodule.subset_span (short_corrected_basis_octad k h0 h11)
  simpa only [add_sub_cancel_right] using (markedShortSpan.sub_mem hc ha)

theorem marked_short_octads_span : markedShortSpan = (golayTwoCoordinateProjection ((0,0),0) ((0,0),1)).ker := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro c hc
    exact Prod.ext hc.1 hc.2.1
  · intro c hc
    have h0 := congrArg Prod.fst hc
    have h1 := congrArg Prod.snd hc
    have he : markedShortProjection c = c := by
      change c - c.val ((0,0),0) • golayBasis 11 - c.val ((0,0),1) • golayBasis 0 = c
      change c.val ((0,0),0) = 0 at h0
      change c.val ((0,0),1) = 0 at h1
      rw [h0,h1,zero_smul,zero_smul,sub_zero,sub_zero]
    rw [← he,← golayBasis.sum_repr c,map_sum]
    apply Submodule.sum_mem
    intro k _
    rw [map_smul]
    exact Submodule.smul_mem _ _ (short_projected_basis_mem k)

end Atlas.Conway
