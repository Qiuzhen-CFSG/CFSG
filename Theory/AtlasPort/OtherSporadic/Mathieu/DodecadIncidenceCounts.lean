/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadComplement
public import Theory.AtlasPort.OtherSporadic.Mathieu.OctadPairCounts

/-!
# Incidence counts for octads and dodecads

There are 506 octads avoiding a fixed coordinate, and 1288 dodecads
through or avoiding it. Octad counts follow by subtraction; complementation
pairs the two dodecad families.

Source: `Atlas/Mathieu/DodecadIncidenceCounts.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octads_avoiding_point_card (a : Omega) :
    (octads.filter (fun O => a ∉ O)).card = 506 := by
  have h := Finset.card_filter_add_card_filter_not (s := octads) (fun O => a ∈ O)
  rw [octads_through_point_card,octads_card] at h
  omega

/-- Complementation pairs the dodecads through a coordinate with those avoiding it. -/
theorem dodecads_through_avoiding_card (a : Omega) :
    (dodecads.filter (fun D => a ∈ D)).card =
      (dodecads.filter (fun D => a ∉ D)).card := by
  apply Finset.card_bij (fun D _ => Dᶜ)
  · intro D hD
    obtain ⟨hD,ha⟩ := Finset.mem_filter.mp hD
    exact Finset.mem_filter.mpr ⟨dodecad_complement D hD,by simpa⟩
  · intro D hD E hE he
    exact compl_injective he
  · intro D hD
    obtain ⟨hD,ha⟩ := Finset.mem_filter.mp hD
    refine ⟨Dᶜ,Finset.mem_filter.mpr ⟨dodecad_complement D hD,?_⟩,compl_compl D⟩
    simpa using ha

theorem dodecads_through_point_card (a : Omega) :
    (dodecads.filter (fun D => a ∈ D)).card = 1288 := by
  have h := Finset.card_filter_add_card_filter_not (s := dodecads) (fun D => a ∈ D)
  have he := dodecads_through_avoiding_card a
  rw [dodecads_card] at h
  omega

theorem dodecads_avoiding_point_card (a : Omega) :
    (dodecads.filter (fun D => a ∉ D)).card = 1288 := by
  rw [← dodecads_through_avoiding_card,dodecads_through_point_card]

end Atlas.Codes
