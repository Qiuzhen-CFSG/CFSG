/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.OctadExteriorSeparation
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetReconstruction

/-!
# OctadPairNormalization

An octad with two distinct exterior points can be carried to a pair of standard tetrads
with the exterior points in distinct other columns. Sextet reconstruction transports the
separating sextet and preserves its part membership.

Source: `Atlas/Mathieu/OctadPairNormalization.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem sextet_image_part_tetrad (S : UnorderedSextet) (g : Mathieu24CodeModel)
    (hg : g • S = distinguishedUnorderedSextet) (T : Finset Omega) (hT : T ∈ S.val) :
    ∃ i, permuteBlock g.val T = tetrad i := by
  have he : permuteSextetParts g.val S.val = distinguishedUnorderedSextet.val :=
    congrArg Subtype.val hg
  have hm : permuteBlock g.val T ∈ distinguishedUnorderedSextet.val := by
    rw [← he]
    exact Finset.mem_image.mpr ⟨T,hT,rfl⟩
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
  exact ⟨i,hi.symm⟩

theorem sextet_image_same_column (S : UnorderedSextet) (g : Mathieu24CodeModel)
    (hg : g • S = distinguishedUnorderedSextet) (a b : Omega)
    (hab : (g.val a).1 = (g.val b).1) :
    ∃ V ∈ S.val, a ∈ V ∧ b ∈ V := by
  obtain ⟨V,⟨hV,haV⟩,_⟩ := S.prop.partition a
  obtain ⟨i,hi⟩ := sextet_image_part_tetrad S g hg V hV
  have ha : (g.val a).1 = i := (mem_tetrad _ _).mp (by
    rw [← hi]; exact Finset.mem_image.mpr ⟨a,haV,rfl⟩)
  have hb : g.val b ∈ permuteBlock g.val V := by rw [hi]; simp [← hab,ha]
  obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hb
  exact ⟨V,hV,haV,g.val.injective he ▸ hc⟩

theorem octad_exterior_pair_normalize (O : Finset Omega) (hO : O ∈ octads)
    (a b : Omega) (ha : a ∉ O) (hb : b ∉ O) (hab : a ≠ b) :
    ∃ g : Mathieu24CodeModel, ∃ i j : HexIndex,
      i ≠ j ∧ permuteBlock g.val O = tetrad i ∪ tetrad j ∧
      (g.val a).1 ≠ i ∧ (g.val a).1 ≠ j ∧
      (g.val b).1 ≠ i ∧ (g.val b).1 ≠ j ∧ (g.val a).1 ≠ (g.val b).1 := by
  obtain ⟨S,T,hT,U,hU,hTU,hsep⟩ :=
    octad_exterior_pair_separating_sextet O hO a b ha hb hab
  obtain ⟨g,hg⟩ := sextet_equivalent_distinguished S
  obtain ⟨i,hi⟩ := sextet_image_part_tetrad S g hg T hT
  obtain ⟨j,hj⟩ := sextet_image_part_tetrad S g hg U hU
  have he : permuteBlock g.val O = tetrad i ∪ tetrad j := by
    rw [← hTU]
    change (T ∪ U).image g.val = _
    rw [Finset.image_union]
    exact congrArg₂ (· ∪ ·) hi hj
  have hij : i ≠ j := by
    intro hh
    have hcard := permuteBlock_card g.val O
    rw [he,hh,Finset.union_self,tetrad_card,octad_size O hO] at hcard
    omega
  have hga : (g.val a).1 ≠ i ∧ (g.val a).1 ≠ j := by
    have hh : g.val a ∉ permuteBlock g.val O := by
      intro h
      obtain ⟨c,hc,hca⟩ := Finset.mem_image.mp h
      exact ha (g.val.injective hca ▸ hc)
    simpa [he] using hh
  have hgb : (g.val b).1 ≠ i ∧ (g.val b).1 ≠ j := by
    have hh : g.val b ∉ permuteBlock g.val O := by
      intro h
      obtain ⟨c,hc,hcb⟩ := Finset.mem_image.mp h
      exact hb (g.val.injective hcb ▸ hc)
    simpa [he] using hh
  refine ⟨g,i,j,hij,he,hga.1,hga.2,hgb.1,hgb.2,?_⟩
  intro hh
  obtain ⟨V,hV,haV,hbV⟩ := sextet_image_same_column S g hg a b hh
  exact hsep V hV haV hbV

end Atlas.Codes
