module

public import Theory.SpecificGroups.LeechRelated.HSRecognition.Uniqueness.Hexads

/-!
# Incidence coordinates for the rank-three Higman--Sims graph

Split the original vertices into the base point, its 22 neighbors, and its
77 nonneighbors. The natural Mathieu labels and the proved hexad bijection
supply coordinates in the native Witt construction. Triangle-freeness makes
the hexads of adjacent exterior vertices disjoint. These are the edge
implications consumed by the exact graph comparison.

Source: Wales, "Uniqueness of the graph of a rank three group", Pacific
J. Math. 30 (1969), p.274; the hexad construction of Higman and Sims,
Math. Z. 105 (1968), 110--113.
-/

public section
open MulAction
namespace Sporadic.LeechRelated.HS
open Sporadic.Mathieu
attribute [local instance] Classical.propDecidable
noncomputable section

variable {P : Subgroup (Equiv.Perm (Fin 100))} (h : RankThreeData P)

private def partition (x : Fin 100) : Unit ⊕ (h.graph.neighborSet 0 ⊕ h.exterior) :=
  if hx : x = 0 then .inl () else
    if hn : h.graph.Adj 0 x then .inr (.inl ⟨x, hn⟩) else .inr (.inr ⟨x, hx, hn⟩)

private def unpartition : Unit ⊕ (h.graph.neighborSet 0 ⊕ h.exterior) → Fin 100
  | .inl _ => 0
  | .inr (.inl x) => x.val
  | .inr (.inr x) => x.val

/-- The actual root, neighbor, and exterior decomposition of the original points. -/
def RankThreeData.partitionEquiv : Fin 100 ≃ Unit ⊕ (h.graph.neighborSet 0 ⊕ h.exterior) where
  toFun := partition h
  invFun := unpartition h
  left_inv := by
    intro x
    dsimp [partition]
    split_ifs with hx hn
    · exact hx.symm
    · rfl
    · rfl
  right_inv := by
    rintro (u | (x | x))
    · cases u
      simp [partition, unpartition]
    · have hx : h.graph.Adj 0 x.val := x.property
      simp [partition, unpartition, hx, hx.ne']
    · simp [partition, unpartition, x.property.1, x.property.2]

@[simp] theorem RankThreeData.partitionEquiv_zero : h.partitionEquiv 0 = .inl () := by
  simp [partitionEquiv, partition]

@[simp] theorem RankThreeData.partitionEquiv_neighbor (x : h.graph.neighborSet 0) :
    h.partitionEquiv x.val = .inr (.inl x) := by
  have hx : h.graph.Adj 0 x.val := x.property
  simp [partitionEquiv, partition, hx, hx.ne']

@[simp] theorem RankThreeData.partitionEquiv_exterior (x : h.exterior) :
    h.partitionEquiv x.val = .inr (.inr x) := by
  simp [partitionEquiv, partition, x.property.1, x.property.2]

/-- Triangle-freeness in the original rank-three graph. -/
theorem RankThreeData.no_triangle {x y z : Fin 100} (hxy : h.graph.Adj x y)
    (hxz : h.graph.Adj x z) : ¬h.graph.Adj y z := by
  intro hyz
  have hc := h.graph_stronglyRegular.of_adj x y hxy
  have hn : Nonempty (h.graph.commonNeighbors x y) := ⟨⟨z, hxz, hyz⟩⟩
  have hp := Fintype.card_pos_iff.mpr hn
  omega

/-- Adjacent exterior vertices have disjoint neighbor hexads. -/
theorem RankThreeData.sixSet_disjoint {x y : h.exterior}
    (f : h.graph.neighborSet 0 ≃ Fin 22) (hxy : h.graph.Adj x.val y.val) :
    Disjoint (h.sixSet f x) (h.sixSet f y) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  exact h.no_triangle hxy ((h.mem_sixSet f x a).mp ha) ((h.mem_sixSet f y a).mp hb)

variable (e : stabilizer P (0 : Fin 100) ≃* M22)
  (f : h.graph.neighborSet 0 ≃ Fin 22)
  (hf : ∀ (g : stabilizer P (0 : Fin 100)) (x y : Fin 100)
    (hx : h.graph.Adj 0 x) (hy : h.graph.Adj 0 y),
    g • x = y → f ⟨y, hy⟩ = e g • f ⟨x, hx⟩)

/-- Incidence coordinates on all one hundred vertices, with native hexad labels. -/
def RankThreeData.wittCoordinates : Fin 100 ≃ Unit ⊕ (Fin 22 ⊕ {B // B ∈ m22Blocks}) :=
  h.partitionEquiv.trans
    (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr f (h.hexadEquiv e f hf)))

@[simp] theorem RankThreeData.wittCoordinates_zero : h.wittCoordinates e f hf 0 = .inl () := by
  simp [wittCoordinates]

@[simp] theorem RankThreeData.wittCoordinates_neighbor (x : h.graph.neighborSet 0) :
    h.wittCoordinates e f hf x.val = .inr (.inl (f x)) := by
  simp [wittCoordinates]

@[simp] theorem RankThreeData.wittCoordinates_exterior (x : h.exterior) :
    h.wittCoordinates e f hf x.val = .inr (.inr (h.hexadEquiv e f hf x)) := by
  simp [wittCoordinates]

end
end Sporadic.LeechRelated.HS
