module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.SourceConclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneSource

/-!
# The actual critical-path Sylow product

At the first edge of a shortest critical path, the opposite center lies in
its neighboring vertex core. The already proved Sylow product therefore
fills that edge's two-core. This proves the equality in DGS (7.1)(c), not
just Sylow membership, and gives the literal set product.

At either base vertex the reduced-completion inclusion carries this group
to the original full Borel core. The index of the original parabolic core
in that Borel core is the defining field order of any actual critical SL₂
marking. No identification of the original F1.11 S with O₂(B) is made.

The genuine enlarged-quotient models remain an earlier Chapter 6 input.
Their outstanding order-144 case is retained by the source assembly owner.
Source: DGS, *Groups and Graphs* (1985), (7.1)(a,c), pp.126--127,
and the original-to-reduced subgroup conventions on pp.95--96.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The critical center fills the actual first edge core along a shortest path. -/
theorem graph_critical_product_eq_edge_core (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    {v u w : Vertex (family P)} (he : (graph (family P)).Adj v u)
    (hd : (graph (family P)).dist u w + 1 = b (family P))
    (hs : Stellmacher.IsSylowSubgroupIn (Z (family P) w ⊔ Q (family P) v)
      (stabilizer (family P) v)) :
    Z (family P) w ⊔ Q (family P) v =
      (stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2 := by
  have hZ : Z (family P) w ≤ Q (family P) u :=
    graph_Z_le_Q_of_short h hS (by rw [SimpleGraph.dist_comm]; omega)
  have hZu := hZ.trans (graph_Q_le_edgeCore h he.symm)
  rw [inf_comm] at hZu
  exact sylow_join_eq_of_le _ _ _ _ hs (isPGroup_pCoreIn 2 _)
    ((pCoreIn_le 2 _).trans inf_le_left) hZu (graph_Q_le_edgeCore h he)

namespace Reduction
open DGS85.Reduction NoncommutingProfile
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- Construct the critical product at any chosen first edge of a shortest path. -/
theorem reduced_critical_product_eq_edge_core (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v u w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (he : (graph F).Adj v u) (hd : (graph F).dist u w + 1 = b F) :
    Z F w ⊔ Q F v = (stabilizer F v ⊓ stabilizer F u).pCoreIn 2 :=
  graph_critical_product_eq_edge_core (reduced_triple h) (reduced_kernel_sylow h) he hd
    (reduced_critical_equal_field_natural_centers h hm hc hne).2.1

/-- The source product is actual multiplication of the two embedded subgroups. -/
theorem reduced_critical_edge_set_product (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v u w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (he : (graph F).Adj v u) (hd : (graph F).dist u w + 1 = b F) :
    (↑((stabilizer F v ⊓ stabilizer F u).pCoreIn 2) : Set (G₀ L₀ S₀)) =
      (Z F w : Set (G₀ L₀ S₀)) * (Q F v : Set (G₀ L₀ S₀)) := by
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  rw [←reduced_critical_product_eq_edge_core h hm hc hne he hd]
  apply coe_mul_of_left_le_normalizer_right
  exact (criticalPair_centers F (reduced_triple h).generate hc).1.trans
    ((stabilizer F v).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

/-- Both base-edge orientations retain the same original full Borel core. -/
theorem reduced_base_edge_core_map (h : HypothesisF11 L₀ S₀) (i : Bool) :
    ((stabilizer F (base F i) ⊓ stabilizer F (base F (!i))).pCoreIn 2).map (G₀ L₀ S₀).subtype =
      (commonBorel L₀ S₀).pCoreIn 2 := by
  have hE : stabilizer F (base F i) ⊓ stabilizer F (base F (!i)) =
      (B₀ L₀ S₀).subgroupOf (G₀ L₀ S₀) := by
    simp only [stabilizer,Subgroup.CosetGeometry.stabilizer_base]
    cases i
    · exact (reduced_triple h).intersection
    · exact (inf_comm _ _).trans (reduced_triple h).intersection
  rw [hE,map_pCoreIn_of_injective 2 _ _ (G₀ L₀ S₀).subtype_injective,
    map_subgroupOf_eq_of_le (show B₀ L₀ S₀ ≤ G₀ L₀ S₀ from le_sup_right.trans le_sup_left),B₀_core h]

/-- Source (7.1)(c) in the original completion, with either vertex orientation. -/
theorem original_critical_product_eq_borel_core (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    (i : Bool) {w : Vertex F} (hc : IsCriticalPair F (base F i) w)
    (hne : ⁅Z F (base F i),Z F w⁆ ≠ ⊥)
    (hd : (graph F).dist (base F (!i)) w + 1 = b F) :
    (Z F w).map (G₀ L₀ S₀).subtype ⊔ (parabolic L₀ S₀ (if i then 1 else 0)).pCoreIn 2 =
      (commonBorel L₀ S₀).pCoreIn 2 := by
  have he : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hp := congrArg (map (G₀ L₀ S₀).subtype)
    (reduced_critical_product_eq_edge_core h hm hc hne he hd)
  rwa [Subgroup.map_sup,reduced_base_Q_map h i,reduced_base_edge_core_map h i] at hp

/-- The chosen edge index gives the field order of any actual critical marking. -/
theorem reduced_critical_edge_index (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v u w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (he : (graph F).Adj v u) (hd : (graph F).dist u w + 1 = b F)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (π : graphLocalGroup F v →* SL(2,k)) (hπ : Function.Surjective π)
    (hk : π.ker = (Q F v).subgroupOf (graphLocalGroup F v)) :
    (Q F v).relIndex ((stabilizer F v ⊓ stabilizer F u).pCoreIn 2) = Nat.card k := by
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  rw [←reduced_critical_product_eq_edge_core h hm hc hne he hd]
  have hZ : Z F w ≤ stabilizer F v :=
    (criticalPair_centers F (reduced_triple h).generate hc).1
  have hQ : Q F v ≤ stabilizer F v := pCoreIn_le 2 _
  let : ((Q F v).subgroupOf (stabilizer F v)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQ).mpr
      ((stabilizer F v).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hi := relIndex_sup_right ((Z F w).subgroupOf (stabilizer F v))
    ((Q F v).subgroupOf (stabilizer F v))
  rw [←subgroupOf_sup hZ hQ,relIndex_subgroupOf (sup_le hZ hQ),relIndex_subgroupOf hZ] at hi
  rw [hi]
  exact (reduced_critical_field_order_eq_index h hm hc hne π hπ hk).symm

/-- The marked q is the index of the original parabolic core in the full Borel core. -/
theorem original_critical_borel_core_index (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    (i : Bool) {w : Vertex F} (hc : IsCriticalPair F (base F i) w)
    (hne : ⁅Z F (base F i),Z F w⁆ ≠ ⊥)
    (hd : (graph F).dist (base F (!i)) w + 1 = b F)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (π : graphLocalGroup F (base F i) →* SL(2,k)) (hπ : Function.Surjective π)
    (hk : π.ker = (Q F (base F i)).subgroupOf (graphLocalGroup F (base F i))) :
    ((parabolic L₀ S₀ (if i then 1 else 0)).pCoreIn 2).relIndex
      ((commonBorel L₀ S₀).pCoreIn 2) = Nat.card k := by
  have he : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  rw [←reduced_base_Q_map h i,←reduced_base_edge_core_map h i,
    relIndex_map_map_of_injective _ _ (G₀ L₀ S₀).subtype_injective]
  exact reduced_critical_edge_index h hm hc hne he hd π hπ hk

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
