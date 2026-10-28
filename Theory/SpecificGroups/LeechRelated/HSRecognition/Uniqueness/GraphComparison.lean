module

public import Theory.SpecificGroups.LeechRelated.HSRecognition.Uniqueness.Coordinates
public import Theory.SpecificGroups.LeechRelated.HSRecognition.Uniqueness.WittModel

/-!
# Unconditional comparison with the exact ATLAS graph

The recovered root, point, and hexad coordinates send every original edge
to an edge of the fixed ATLAS graph: root--point edges, point--hexad
incidence, and disjoint-hexad edges. Both graphs have degree 22, so the
bijection maps each entire neighborhood onto the corresponding neighborhood
and therefore also reflects adjacency. All Mathieu and coordinate witnesses
are constructed from `RankThreeData`; no extra geometric premise remains.

This completes the graph part of Wales's HS uniqueness application,
Pacific J. Math. 30 (1969), p.274. Equality of degrees replaces the character
calculation of the remaining 77-point suborbit: triangle-freeness already
forces every edge into the explicit target graph.
-/

public section
open MulAction
namespace Sporadic.LeechRelated.HS
open Sporadic.Mathieu NormalizerIndex
attribute [local instance] Classical.propDecidable
noncomputable section

variable {P : Subgroup (Equiv.Perm (Fin 100))} (h : RankThreeData P)
  (e : stabilizer P (0 : Fin 100) ≃* M22)
  (f : h.graph.neighborSet 0 ≃ Fin 22)
  (hf : ∀ (g : stabilizer P (0 : Fin 100)) (x y : Fin 100)
    (hx : h.graph.Adj 0 x) (hy : h.graph.Adj 0 y),
    g • x = y → f ⟨y, hy⟩ = e g • f ⟨x, hx⟩)

private theorem model_forward : ∀ x y : Fin 100, h.graph.Adj x y →
    adjacency (WittModel.modelEquiv (h.wittCoordinates e f hf x))
      (WittModel.modelEquiv (h.wittCoordinates e f hf y)) := by
  intro x y hxy
  by_cases hx : x = 0
  · subst x
    rw [h.wittCoordinates_zero, h.wittCoordinates_neighbor e f hf ⟨y, hxy⟩]
    exact WittModel.root_point _
  by_cases hy : y = 0
  · subst y
    rw [h.wittCoordinates_zero, h.wittCoordinates_neighbor e f hf ⟨x, hxy.symm⟩]
    exact (adjacency_symm _ _).mpr (WittModel.root_point _)
  by_cases hxn : h.graph.Adj 0 x
  · by_cases hyn : h.graph.Adj 0 y
    · exact (h.no_triangle hxn hyn hxy).elim
    · let a : h.graph.neighborSet 0 := ⟨x, hxn⟩
      let b : h.exterior := ⟨y, hy, hyn⟩
      rw [h.wittCoordinates_neighbor e f hf a, h.wittCoordinates_exterior e f hf b]
      apply WittModel.point_block
      change f a ∈ h.sixSet f b
      rw [h.mem_sixSet, f.symm_apply_apply]
      exact hxy.symm
  · let a : h.exterior := ⟨x, hx, hxn⟩
    by_cases hyn : h.graph.Adj 0 y
    · let b : h.graph.neighborSet 0 := ⟨y, hyn⟩
      rw [h.wittCoordinates_exterior e f hf a, h.wittCoordinates_neighbor e f hf b]
      apply (adjacency_symm _ _).mpr
      apply WittModel.point_block
      change f b ∈ h.sixSet f a
      rw [h.mem_sixSet, f.symm_apply_apply]
      exact hxy
    · let b : h.exterior := ⟨y, hy, hyn⟩
      rw [h.wittCoordinates_exterior e f hf a, h.wittCoordinates_exterior e f hf b]
      exact WittModel.block_block _ _ (h.sixSet_disjoint f hxy)

/-- A vertex bijection carrying edges between graphs of the same degree also reflects edges. -/
private theorem reflects_adjacency (E : Fin 100 ≃ Fin 100)
    (hE : ∀ x y, h.graph.Adj x y → adjacency (E x) (E y)) :
    ∀ x y, adjacency (E x) (E y) ↔ h.graph.Adj x y := by
  intro x y
  refine ⟨?_, hE x y⟩
  intro hxy
  have hsub : (h.graph.neighborFinset x).image E ⊆ neighbors (E x) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact (mem_neighbors _ _).mpr (hE x w ((h.graph.mem_neighborFinset x w).mp hw))
  have heq : (h.graph.neighborFinset x).image E = neighbors (E x) :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [neighbors_card, Finset.card_image_of_injective _ E.injective]
      exact le_of_eq (h.graph_stronglyRegular.regular x).symm)
  have hy : E y ∈ (h.graph.neighborFinset x).image E :=
    heq ▸ (mem_neighbors _ _).mpr hxy
  obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
  exact E.injective hzy ▸ (h.graph.mem_neighborFinset x z).mp hz

omit e f hf in
/-- The canonical rank-three graph is the exact ATLAS graph, up to an actual
bijection on the original one hundred vertices. -/
theorem RankThreeData.exists_graph_equiv : ∃ E : Fin 100 ≃ Fin 100,
    ∀ x y, adjacency (E x) (E y) ↔ h.graph.Adj x y := by
  obtain ⟨e⟩ := h.stabilizer_model
  obtain ⟨f, hf⟩ := h.neighbor_coordinates e
  let E := (h.wittCoordinates e f hf).trans WittModel.modelEquiv
  exact ⟨E, reflects_adjacency h E (model_forward h e f hf)⟩

end
end Sporadic.LeechRelated.HS
