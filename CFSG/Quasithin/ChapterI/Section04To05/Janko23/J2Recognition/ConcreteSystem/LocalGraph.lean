module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.ConcreteSystem
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicEdges

/-!
# The induced local graph in the concrete J₂ system

The local edge orbit of the completed system is exactly the induced graph
on the order-three vertices contained in its literal subgroup K = C(B).
Restriction to K preserves the subgroup joins and conjugation. The proved
A₅ ordered-edge transitivity then supplies an actual K transporter.

This identifies `System.localGraph` with the graph called Δ_K in
Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267. It imposes no
connectivity condition on the target graph.
-/

public section
namespace CFSG.Quasithin.Janko23.J2Recognition.ConcreteSystem
open Subgroup Theory.GroupTheory.GraphUniquenessSystem
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.RecognitionGeometry
open scoped Pointwise

private theorem X_le_K : X ≤ K := le_sup_left.trans X_sup_Y_le_K

private theorem Y_le_K : Y ≤ K := le_sup_right.trans X_sup_Y_le_K

private noncomputable def joinInLocalEquiv (A B : Subgroup Carrier)
    (hA : A ≤ K) (hB : B ≤ K) :
    ↥(A.subgroupOf K ⊔ B.subgroupOf K) ≃* ↥(A ⊔ B) :=
  ((A.subgroupOf K ⊔ B.subgroupOf K).equivMapOfInjective K.subtype
    K.subtype_injective).trans (MulEquiv.subgroupCongr (by
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB]))

private theorem card_inLocal (A : Vertex) (hA : A.val ≤ K) :
    Nat.card (A.val.subgroupOf K) = 3 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv, vertex_card]

private theorem smul_of_local_conj (A B : Vertex) (hA : A.val ≤ K) (hB : B.val ≤ K)
    (g : K) (hg : (A.val.subgroupOf K).map (MulAut.conj g).toMonoidHom = B.val.subgroupOf K) :
    (g : Carrier) • A = B := by
  change MulAut.conj g • A.val.subgroupOf K = B.val.subgroupOf K at hg
  rw [conj_smul_subgroupOf hA g] at hg
  have hm := congrArg (fun U : Subgroup K => U.map K.subtype) hg
  rw [map_subgroupOf_eq_of_le (conj_smul_le_of_le hA g),
    map_subgroupOf_eq_of_le hB] at hm
  exact Subtype.ext hm

/-- Every induced ordered edge inside K has a transporter in that same K. -/
theorem local_ordered_edge_transitive (A B : Vertex) (hAB : graph.Adj A B)
    (hA : A.val ≤ K) (hB : B.val ≤ K) :
    ∃ g : K, (g : Carrier) • base = A ∧ (g : Carrier) • neighbor = B := by
  obtain ⟨eAB⟩ := (graph_adj_iff A B).mp hAB
  obtain ⟨g, hg, hg'⟩ := alternatingGroup.FiveLocalGeometry.CubicEdges.ordered_edge_transitive
    LocalA5.localEquiv (X.subgroupOf K) (Y.subgroupOf K)
    (A.val.subgroupOf K) (B.val.subgroupOf K)
    (card_inLocal base X_le_K) (card_inLocal neighbor Y_le_K)
    (card_inLocal A hA) (card_inLocal B hB)
    ((joinInLocalEquiv X Y X_le_K Y_le_K).trans edgeEquiv)
    ((joinInLocalEquiv A.val B.val hA hB).trans eAB)
  exact ⟨g, smul_of_local_conj base A X_le_K hA g hg,
    smul_of_local_conj neighbor B Y_le_K hB g hg'⟩

/-- The literal local edge orbit agrees with the source's induced graph Δ_K. -/
theorem system_localEdge_iff (A B : Vertex) :
    system.localEdge A B ↔ graph.Adj A B ∧ A.val ≤ K ∧ B.val ≤ K := by
  rw [System.localEdge, system_local, system_base, system_neighbor]
  constructor
  · rintro ⟨g, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨preserves g adjacent, conj_smul_le_of_le X_le_K g,
        conj_smul_le_of_le Y_le_K g⟩
    · exact ⟨(preserves g adjacent).symm, conj_smul_le_of_le Y_le_K g,
        conj_smul_le_of_le X_le_K g⟩
  · rintro ⟨hAB, hA, hB⟩
    obtain ⟨g, hg⟩ := local_ordered_edge_transitive A B hAB hA hB
    exact ⟨g, Or.inl hg⟩

end CFSG.Quasithin.Janko23.J2Recognition.ConcreteSystem
