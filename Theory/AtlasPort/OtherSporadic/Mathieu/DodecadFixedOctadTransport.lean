/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadFixedOctad
public import Theory.AtlasPort.OtherSporadic.Mathieu.GolaySmallSetFixing

/-!
# DodecadFixedOctadTransport

For any four-set inside a dodecad, there is a dodecad-preserving automorphism whose
exact fixed set is an octad meeting the dodecad in that four-set. Normalize the four-set
as a tetrad and conjugate the explicit local translation back.

Source: `Atlas/Mathieu/DodecadFixedOctadTransport.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem permuteBlock_apply_mem (g : Equiv.Perm Omega) (S : Finset Omega) (z : Omega) :
    g z ∈ permuteBlock g S ↔ z ∈ S := by
  change g z ∈ S.image g ↔ _
  constructor
  · intro hz
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hz
    exact g.injective he ▸ hu
  · intro hz
    exact Finset.mem_image.mpr ⟨z,hz,rfl⟩

theorem dodecad_fixed_octad (D : Dodecad) (T : FourSet) (hTD : T.val ⊆ D.val) :
    ∃ g : Mathieu24CodeModel, ∃ O ∈ octads,
      permuteBlock g.val D.val = D.val ∧ (∀ z, g.val z = z ↔ z ∈ O) ∧
      (∀ z, z ∈ O ∧ z ∈ D.val ↔ z ∈ T.val) := by
  let i : HexIndex := (0,0)
  obtain ⟨q,_,hq⟩ := mathieu24_fixing_small_set_transitive ∅ T.val (tetrad i) 4
    (by simp) (by simp) T.prop (tetrad_card i) (by simp)
  let D' : DodecadsThroughTetrad i := ⟨⟨permuteBlock q.val D.val,
    codePreserving_dodecad_forward _ q.prop _ D.prop⟩,by
      rw [← hq]; exact Finset.image_subset_image hTD⟩
  obtain ⟨p,hp⟩ := (dodecadParametersSupport_bijective i).2 D'
  obtain ⟨s,O,hO,hD,hs,hint⟩ := dodecad_local_fixed_octad i p
  have hp' : (dodecadParametersSupport i p).val.val = permuteBlock q.val D.val :=
    congrArg (fun E : DodecadsThroughTetrad i => E.val.val) hp
  rw [hp'] at hD hint
  let P := permuteBlock q.val⁻¹ O
  have hP : P ∈ octads := (codePreserving_octadPreserving (q⁻¹).val (q⁻¹).prop O).mp hO
  have hPm (z : Omega) : z ∈ P ↔ q.val z ∈ O := by
    change z ∈ O.image q.val.symm ↔ _
    constructor
    · rintro hz
      obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hz
      rw [← he]
      simpa using hu
    · intro hz
      exact Finset.mem_image.mpr ⟨q.val z,hz,q.val.symm_apply_apply z⟩
  refine ⟨q⁻¹*s*q,P,hP,?_,?_,?_⟩
  · change permuteBlock (q.val⁻¹*s.val*q.val) D.val = D.val
    rw [permuteBlock_mul,permuteBlock_mul,hD,← permuteBlock_mul,inv_mul_cancel,permuteBlock_one]
  · intro z
    change q.val.symm (s.val (q.val z)) = z ↔ _
    rw [q.val.symm_apply_eq,hs,hPm]
  · intro z
    rw [hPm,← permuteBlock_apply_mem q.val D.val z,hint,← hq,permuteBlock_apply_mem]

end Atlas.Codes
