module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.ConcreteSystem.TriangleCertificate.Checks
public import Theory.GroupTheory.Amalgam.UniquenessSystem.RankedTriangles

/-!
# Triangle simple connectivity of the literal J₂ graph

The certified 36-neighbor rows are exhaustive because the already proved word
action is a permutation of all 280 subgroup vertices. The finite rank checks
therefore apply to every actual A₄-join edge. The depth-two spanning-tree
contraction then proves triangle simple connectivity of the subgroup graph.

Source: Aschbacher, *Sporadic Groups* (1994), §§34–37 and 47. This supplies
the target cycle-base route to the arbitrary-source recognition theorem.
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.TriangleCertificate
open OrbitAction OrbitAction.Data GeneratorPair FirstFusion
open Subgroup Theory.GroupTheory
open scoped Pointwise

theorem actWord_smul (w : List (Fin 3)) (i : Fin 280) :
    evalWord letter w • vertex i = vertex (actWord w i) := by
  induction w generalizing i with
  | nil => simp [evalWord, actWord]
  | cons s w ih =>
    rw [evalWord, mul_smul, ih, actWord]
    have h := vertex_step (actWord w i) (invLetter s)
    simpa only [letter_inv, inv_inv] using h

private theorem isNeighbor_iff (i : Fin 280) :
    isNeighbor i = true ↔ graph.Adj base (vertex i) := by
  constructor
  · intro hi
    have h : ∀ i, isNeighbor i = true → ∃ j : Fin 36, neighborRow j = i := by
      decide +kernel
    obtain ⟨j, rfl⟩ := h i hi
    exact listed_neighbor_adjacent j
  · exact adjacent_isNeighbor i

/-- The finite word action retains the literal A₄-join adjacency. -/
theorem adjBool_iff (i j : Fin 280) : adjBool i j = true ↔ graph.Adj (vertex i) (vertex j) := by
  rw [adjBool, isNeighbor_iff, ← actWord_smul]
  change graph.Adj base (rep i • vertex j) ↔ _
  constructor
  · intro h
    have h' := preserves (rep i)⁻¹ h
    simpa only [vertex, inv_smul_smul] using h'
  · intro h
    have h' := preserves (rep i) h
    simpa only [vertex, smul_inv_smul] using h'

private theorem actWord_injective (w : List (Fin 3)) : Function.Injective (actWord w) := by
  intro i j hij
  apply vertex_injective
  apply (MulAction.toPerm (evalWord letter w)).injective
  change evalWord letter w • vertex i = evalWord letter w • vertex j
  rw [actWord_smul, actWord_smul, hij]

/-- Each listed neighbor is a conjugate of a previously certified base neighbor. -/
theorem neighbor_adj (i : Fin 280) (k : Fin 36) :
    graph.Adj (vertex i) (vertex (neighborIndex i k)) := by
  apply (adjBool_iff _ _).mp
  change isNeighbor (actWord (words i) (neighborIndex i k)) = true
  rw [neighbor_spec]
  exact adjacent_isNeighbor _ (listed_neighbor_adjacent k)

/-- The word action is a permutation, so the 36 checked images exhaust the
actual neighbors. No new finite order or simplicity assumption is used. -/
theorem neighbors_iff (i j : Fin 280) : graph.Adj (vertex i) (vertex j) ↔
    ∃ k, neighborIndex i k = j := by
  constructor
  · intro hij
    have hn := (adjBool_iff i j).mpr hij
    have h : ∀ i, isNeighbor i = true → ∃ k : Fin 36, neighborRow k = i := by
      decide +kernel
    obtain ⟨k, hk⟩ := h _ hn
    exact ⟨k, actWord_injective (words i) ((neighbor_spec i k).trans hk)⟩
  · rintro ⟨k, rfl⟩
    exact neighbor_adj i k

abbrev indexedGraph : SimpleGraph (Fin 280) := graph.comap vertex

/-- The actual indexed graph has the checked decreasing triangle reduction. -/
theorem indexed_simplyConnected : indexedGraph.TriangleSimplyConnected := by
  have ht (i : Fin 280) : parent (parent i) = 0 ∧
      (i ≠ 0 → indexedGraph.Adj (parent i) i) ∧
      (parent i ≠ 0 → indexedGraph.Adj 0 (parent i)) := by
    refine ⟨(tree_data i).1, ?_, ?_⟩
    · intro hi
      exact (neighbors_iff _ _).mpr ⟨treeIndex i, (tree_data i).2.1 hi⟩
    · intro hi
      exact (neighbors_iff _ _).mpr ⟨rootIndex i, (tree_data i).2.2 hi⟩
  apply SimpleGraph.TwoStepTree.simplyConnected (Γ := indexedGraph) 0 parent
    (by decide +kernel) ht rank
  · intro i j hij hr
    obtain ⟨k, rfl⟩ := (neighbors_iff _ _).mp hij
    exact (reduction_data i k).1 hr
  · intro i j hij hr
    obtain ⟨k, rfl⟩ := (neighbors_iff _ _).mp hij
    obtain ⟨h₁, h₂, h₃, h₄⟩ := (reduction_data i k).2 hr
    exact ⟨pivot i (neighborIndex i k),
      (neighbors_iff _ _).mpr ⟨leftIndex i k, h₁⟩,
      (neighbors_iff _ _).mpr ⟨rightIndex i k, h₂⟩, h₃, h₄⟩

/-- Triangle simple connectivity of the literal ATLAS subgroup graph. -/
theorem simplyConnected : graph.TriangleSimplyConnected := by
  let e : indexedGraph ≃g graph := {
    toEquiv := vertexEquiv
    map_rel_iff' := by intro i j; rfl }
  exact SimpleGraph.TriangleSimplyConnected.of_iso e indexed_simplyConnected

end Sporadic.LeechRelated.J2.RecognitionGeometry.TriangleCertificate
