/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/ConwaySimplicity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.QuotientGolaySigns
public import Theory.AtlasPort.OtherSporadic.GroupTheory.IwasawaStabilizer

/-!
Simplicity of the central quotient of the Leech isometry group.
The proof uses the faithful primitive cross action and the normally generating abelian sign subgroup.

Source: Gerald Höhn, `Atlas/Conway/ConwaySimplicity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem leechCentralQuotient_noncommuting_pair :
    ∃ g h : LeechCentralQuotient, g*h ≠ h*g := by
  obtain ⟨g,h,hgh⟩ := mathieu24_noncommuting_pair
  refine ⟨quotientPermutationEmbedding g,quotientPermutationEmbedding h,?_⟩
  intro he
  apply hgh
  apply quotientPermutationEmbedding_injective
  simpa only [map_mul] using he

theorem leechCentralQuotient_simple : IsSimpleGroup LeechCentralQuotient := by
  let := quotient_cross_faithful
  let := quotient_cross_primitive
  let := leechCentralQuotient_perfect
  let := mathieu24_simple
  let : Nontrivial LeechCentralQuotient :=
    Function.Injective.nontrivial quotientPermutationEmbedding_injective
  apply Atlas.GroupTheory.iwasawa_stabilizer_simple standardCross quotientGolaySignSubgroup
  · rw [quotient_cross_stabilizer]
    exact quotientGolaySignSubgroup_le_monomial
  · rw [quotient_cross_stabilizer]
    exact quotientGolaySignSubgroup_normal
  · exact quotientGolaySignSubgroup_abelian
  · exact quotientGolaySigns_normalClosure_eq_full

theorem leechCentralQuotient_normal_subgroups (L : Subgroup LeechCentralQuotient) [hL : L.Normal] :
    L = ⊥ ∨ L = ⊤ := by
  let := leechCentralQuotient_simple
  exact hL.eq_bot_or_eq_top

theorem leechCentralQuotient_center : Subgroup.center LeechCentralQuotient = ⊥ := by
  rcases leechCentralQuotient_normal_subgroups (Subgroup.center LeechCentralQuotient) with he | he
  · exact he
  · have hc := (Subgroup.center_eq_top_iff).mp he
    let := hc
    obtain ⟨g,h,hgh⟩ := leechCentralQuotient_noncommuting_pair
    exact (hgh (mul_comm' g h)).elim

theorem leechIsometryGroup_not_simple : ¬ IsSimpleGroup LeechIsometryGroup := by
  intro hG
  let := hG
  rcases (inferInstance : leechCentralSigns.Normal).eq_bot_or_eq_top with he | he
  · have hc := leechCentralSigns_card
    rw [he,Subgroup.card_bot] at hc
    omega
  · have hc := leechCentralSigns_card
    rw [he,Subgroup.card_top,leechIsometryGroup_order] at hc
    omega

end Atlas.Conway
