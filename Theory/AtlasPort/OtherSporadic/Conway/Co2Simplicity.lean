/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co2Simplicity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co2LineFaithfulness
public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway2Generation
public import Theory.AtlasPort.OtherSporadic.GroupTheory.IwasawaStabilizer

/-!
Simplicity of the full stabilizer of the specified norm-four Leech vector.
The proof applies Iwasawa to the faithful primitive orthogonal-line action and its normally generating signs.

Source: Gerald Höhn, `Atlas/Conway/Co2Simplicity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
set_option maxRecDepth 10000

theorem co2Signs_le_local : co2Signs ≤ Atlas.Sporadic.Conway2.LocalGroup := by
  rintro g ⟨h,_,rfl⟩
  exact h.prop

theorem co2Signs_subgroupOf :
    co2Signs.subgroupOf Atlas.Sporadic.Conway2.LocalGroup = Atlas.Sporadic.Conway2.signs := by
  change co2Signs.comap (orthogonalLineStabilizer ((0,0),0) ((0,0),1)).subtype =
    orthogonalLineSigns ((0,0),0)
      ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨h,hh,he⟩
    have he' : h = g := Subtype.ext he
    rwa [← he']
  · intro hg
    exact ⟨g,hg,rfl⟩

theorem co2Signs_abelian : IsMulCommutative co2Signs := by
  refine ⟨⟨fun g h => ?_⟩⟩
  obtain ⟨g',hg,he⟩ := g.prop
  obtain ⟨h',hh,hf⟩ := h.prop
  apply Subtype.ext
  change g.val*h.val = h.val*g.val
  rw [← he,← hf]
  exact congrArg (fun k : Atlas.Sporadic.Conway2.LocalGroup => k.val)
    (congrArg Subtype.val (Atlas.Sporadic.Conway2.signs_commute ⟨g',hg⟩ ⟨h',hh⟩))

theorem co2_simple : IsSimpleGroup Co2MarkedModel := by
  have := co2_lines_faithful
  have := Atlas.Sporadic.Conway2.primitive
  have := Atlas.Sporadic.Conway2.perfect
  have : Nontrivial Co2MarkedModel := by
    obtain ⟨g,h,hh⟩ := co2_noncommuting_pair
    exact ⟨⟨g*h,h*g,hh⟩⟩
  apply Atlas.GroupTheory.iwasawa_stabilizer_simple Atlas.Sporadic.Conway2.basePoint co2Signs
  · rw [Atlas.Sporadic.Conway2.full_point_stabilizer]
    exact co2Signs_le_local
  · rw [Atlas.Sporadic.Conway2.full_point_stabilizer,co2Signs_subgroupOf]
    exact Atlas.Sporadic.Conway2.signs_normal
  · exact co2Signs_abelian
  · exact co2Signs_normalClosure

end Atlas.Conway
