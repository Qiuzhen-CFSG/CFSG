/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadFixedOctadTransport
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetCompletion

/-!
# DodecadMixedNoFixedPoint

For an interior point of a dodecad and an exterior coordinate, some dodecad-stabilizer
element fixes the interior point and moves the exterior coordinate. The fixed-octad
geometry and coordinate transport construct the required element.

Source: `Atlas/Mathieu/DodecadMixedNoFixedPoint.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem dodecad_inside_point_moves_outside (D : Dodecad) (a b : Omega)
    (ha : a ∈ D.val) (hb : b ∉ D.val) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val D.val = D.val ∧ g.val a = a ∧ g.val b ≠ b := by
  by_contra hno
  have hall (g : Mathieu24CodeModel) (hg : permuteBlock g.val D.val = D.val) (hga : g.val a = a) :
      g.val b = b := by
    by_contra hgb
    exact hno ⟨g,hg,hga,hgb⟩
  have he : (D.val.erase a).card = 11 := by
    rw [Finset.card_erase_of_mem ha,dodecad_size _ D.prop]
  obtain ⟨R0,hR0,hcard⟩ := Finset.exists_subset_card_eq (show 2 ≤ (D.val.erase a).card by omega)
  have haR0 : a ∉ R0 := fun h => (Finset.mem_erase.mp (hR0 h)).1 rfl
  let R := insert a R0
  have hR : R.card = 3 := by simp [R,haR0,hcard]
  have hRD : R ⊆ D.val := Finset.insert_subset ha (fun z hz => (Finset.mem_erase.mp (hR0 hz)).2)
  have hbR : b ∉ R := fun h => hb (hRD h)
  let F : FourSet := ⟨insert b R,by simp [hbR,hR]⟩
  have hex (c : {c // c ∈ D.val \ R}) :
      ∃ O ∈ octads, F.val ⊆ O ∧ (∀ z, z ∈ O ∧ z ∈ D.val ↔ z ∈ insert c.val R) := by
    have hc := Finset.mem_sdiff.mp c.prop
    let T : FourSet := ⟨insert c.val R,by simp [hc.2,hR]⟩
    obtain ⟨g,O,hO,hg,hfix,hOD⟩ := dodecad_fixed_octad D T (Finset.insert_subset hc.1 hRD)
    have haT : a ∈ T.val := by simp [T,R]
    have haO : a ∈ O := ((hOD a).mpr haT).1
    have hbO : b ∈ O := (hfix b).mp (hall g hg ((hfix a).mpr haO))
    refine ⟨O,hO,Finset.insert_subset hbO ?_,hOD⟩
    intro z hz
    exact ((hOD z).mpr (Finset.mem_insert_of_mem hz)).1
  choose O hO hFO hOD using hex
  let f : {c // c ∈ D.val \ R} → {U // U ∈ tetradCompanions F} := fun c =>
    ⟨O c \ F.val,(companion_mem F _).mpr ⟨O c,hO c,hFO c,rfl⟩⟩
  have hf : Function.Injective f := by
    intro c d h
    have he : O c \ F.val = O d \ F.val := congrArg Subtype.val h
    have hOcOd : O c = O d := by
      calc
        O c = F.val ∪ (O c \ F.val) := (Finset.union_sdiff_of_subset (hFO c)).symm
        _ = F.val ∪ (O d \ F.val) := by rw [he]
        _ = O d := Finset.union_sdiff_of_subset (hFO d)
    have hcO : c.val ∈ O d := hOcOd ▸ ((hOD c c.val).mpr (by simp)).1
    have hcD := (Finset.mem_sdiff.mp c.prop).1
    have hcR := (Finset.mem_sdiff.mp c.prop).2
    have heq := (hOD d c.val).mp ⟨hcO,hcD⟩
    exact Subtype.ext (by simpa [hcR] using heq)
  have hn := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_coe,Fintype.card_coe,
    companion_count,Finset.card_sdiff_of_subset hRD,dodecad_size _ D.prop,hR] at hn
  norm_num at hn

end Atlas.Codes
