/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadFourInterface
public import Theory.AtlasPort.OtherSporadic.Codes.GolayMarkings

/-!
# DodecadFixedOctad

An explicit nonzero hexacode translation preserves a parametrized dodecad and has an
octad as its exact fixed set. The two zero coordinates determine that octad, whose
intersection with the dodecad is the marked tetrad.

Source: `Atlas/Mathieu/DodecadFixedOctad.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem affine_translation_fixed (h : HexWord) (z : Omega) :
    affinePermutation h 1 z = z ↔ h z.1 = 0 := by
  change (z.1,rowLabel.symm (rowLabel z.2+h z.1)) = z ↔ _
  constructor
  · intro he
    have hh := congrArg (fun z : Omega => rowLabel z.2) he
    simp only [rowLabel.apply_symm_apply] at hh
    exact add_eq_left.mp hh
  · intro hh
    simp [hh]

/-- The nonzero hexacode translation fixes an octad meeting the dodecad in its marked tetrad. -/
theorem dodecad_local_fixed_octad (i : HexIndex) (p : DodecadParameters i) :
    ∃ g : Mathieu24CodeModel, ∃ O ∈ octads,
      permuteBlock g.val (dodecadParametersSupport i p).val.val = (dodecadParametersSupport i p).val.val ∧
      (∀ z, g.val z = z ↔ z ∈ O) ∧
      (∀ z, z ∈ O ∧ z ∈ (dodecadParametersSupport i p).val.val ↔ z ∈ tetrad i) := by
  let h := p.1.val
  obtain ⟨j,hj,huniq⟩ := hexZeroCoordinate_unique_other_zero i h p.1.prop
  let g := (tetradPointStabilizerEquiv i (SemidirectProduct.inl (Multiplicative.ofAdd h))).val
  have hg (z : Omega) : g.val z = affinePermutation h.val.val 1 z := rfl
  have hword : coordinatePermutation g.val (c0Encoder (h.val,p.2.val)) = c0Encoder (h.val,p.2.val) := by
    apply dodecad_translation_word i h h p.2.val p.2.val
    intro k
    have hp : ∀ u : K, polar u u = 0 := by decide
    rw [hp,add_zero]
  refine ⟨g,tetrad i ∪ tetrad j,tetrad_pair_octad i j (Ne.symm hj.1),?_,?_,?_⟩
  · exact (coordinatePermutation_support g.val _).symm.trans (congrArg support hword)
  · intro z
    rw [hg,affine_translation_fixed]
    simp only [Finset.mem_union,mem_tetrad]
    constructor
    · intro hz
      by_cases hi : z.1 = i
      · exact Or.inl hi
      · exact Or.inr (huniq z.1 ⟨hi,hz⟩)
    · rintro (hi | hj')
      · rw [hi]; exact h.prop
      · rw [hj']; exact hj.2
  · intro z
    constructor
    · rintro ⟨hz,hD⟩
      rcases Finset.mem_union.mp hz with hi | hz
      · exact hi
      · have hzj := (mem_tetrad z j).mp hz
        have hr := p.2.prop.2 j hj.1 hj.2
        have hc : c0Encoder (h.val,p.2.val) z = 0 := by
          change Atlas.Codes.j (h.val.val z.1) z.2 + p.2.val.val (hexIndexEquiv z.1) = 0
          rw [hzj,hj.2,hr]
          simp
        exact False.elim ((Finset.mem_filter.mp hD).2 hc)
    · intro hz
      exact ⟨Finset.mem_union_left _ hz,(dodecadParametersSupport i p).prop hz⟩

end Atlas.Codes
