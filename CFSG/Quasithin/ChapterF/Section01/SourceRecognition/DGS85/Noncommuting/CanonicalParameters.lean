module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.ActorData

/-!
# Intrinsic field orders at noncommuting critical endpoints

The literal opposite-center product is a Sylow subgroup of the full vertex
stabilizer. Restrict it to the intrinsic actor and map through any surjective
SL₂ marking with the original two-core kernel. The image is a Sylow of SL₂,
so its defining field order is exactly the opposite-center relative index.
The sharp reciprocal index theorem equates these two indices, independently
of all choices of natural coordinates or quotient markings.

The source applications construct the edge-local actors from their genuine
rank-one quotient models. They require no distance bound, obstruction,
representation-faithfulness or field-equality premise. `SourceConclusion`
uses these identities for both natural centers and the Chapter 10 actions.
Source: DGS, *Groups and Graphs* (1985), (7.1)(a,c), pp.126--127.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G]

private theorem field_card_of_sylow_product
    (P L Q A : Subgroup G) [Finite P] (hLP : L ≤ P) (hQL : Q ≤ L) (hAL : A ≤ L)
    (hs : Stellmacher.IsSylowSubgroupIn (A ⊔ Q) P)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (π : L →* SL(2,k)) (hπ : Function.Surjective π) (hk : π.ker = Q.subgroupOf L) :
    Nat.card k = Q.relIndex A := by
  let : Finite L := Finite.of_injective (inclusion hLP) (inclusion_injective _)
  obtain ⟨T,hT⟩ := hs
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le (H := L) hLP
    (hT ▸ sup_le hAL hQL)
  have hRAQ : (R : Subgroup L) = (A ⊔ Q).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (sup_le hAL hQL)]
    exact hR.trans hT
  let U := R.mapSurjective (f := π) hπ
  have hU : (U : Subgroup SL(2,k)) = (A.subgroupOf L).map π := by
    change (R : Subgroup L).map π = _
    rw [hRAQ,subgroupOf_sup hAL hQL,Subgroup.map_sup,←hk,map_ker_self,sup_bot_eq]
  have hcard : Nat.card ((A.subgroupOf L).map π) = Nat.card k := by
    rw [←hU]
    exact Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 U).symm.toEquiv
  exact hcard.symm.trans (actor_image_card_eq_relIndex L Q A π hk hAL)

namespace Reduction
open DGS85.Reduction
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L₀ S₀ i) (G₀ L₀ S₀))

/-- The sharp quotient-image equality is equality of the literal opposite-core indices. -/
theorem reduced_critical_core_indices_eq_of_localData (h : HypothesisF11 L₀ S₀)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (E₀ E₁ : Subgroup (G₀ L₀ S₀))
    (c₀ : LocalRankOneData (stabilizer F v) E₀)
    (c₁ : LocalRankOneData (stabilizer F w) E₁)
    (ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer F v))
    (ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer F w)) :
    (Q F v).relIndex (Z F w) = (Q F w).relIndex (Z F v) := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let := graph_Z_elementary ht v
  let := graph_Z_elementary ht w
  let : IsElementaryAbelian 2 (Z F v) := graph_Z_elementary ht v
  let : IsElementaryAbelian 2 (Z F w) := graph_Z_elementary ht w
  let : ((Q F v).subgroupOf c₀.Pstar).Normal := graph_local_core_normal v c₀
  let : ((Q F w).subgroupOf c₁.Pstar).Normal := graph_local_core_normal w c₁
  have hc' := (reduced_noncommuting_critical_intersections h hc hne).1
  have h₀ : Z F w ≤ c₀.Pstar := local_twoGroup_le_star c₀ ho₀ _
    (IsElementaryAbelian.isPGroup 2 _) (criticalPair_centers F ht.generate hc).1
  have h₁ : Z F v ≤ c₁.Pstar := local_twoGroup_le_star c₁ ho₁ _
    (IsElementaryAbelian.isPGroup 2 _) (criticalPair_centers F ht.generate hc').1
  let : ((Q (reducedFamily L₀ S₀) v).subgroupOf c₀.Pstar).Normal := graph_local_core_normal v c₀
  let : ((Q (reducedFamily L₀ S₀) w).subgroupOf c₁.Pstar).Normal := graph_local_core_normal w c₁
  have hh := (reduced_critical_quotients_linear_and_indices h hc hne E₀ E₁ c₀ c₁ ho₀ ho₁).2.2
  exact (actor_image_card_eq_relIndex c₀.Pstar (Q F v) (Z F w)
    (QuotientGroup.mk' _) (QuotientGroup.ker_mk' _) h₀).symm.trans
      (hh.trans (actor_image_card_eq_relIndex c₁.Pstar (Q F w) (Z F v)
        (QuotientGroup.mk' _) (QuotientGroup.ker_mk' _) h₁))

/-- The two intrinsic indices agree after constructing the actual local actors. -/
theorem reduced_critical_core_indices_eq (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    (Q F v).relIndex (Z F w) = (Q F w).relIndex (Z F v) := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let d := graphActorLocalData ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hm
  have hd (x y : Vertex F) (he : (graph F).Adj x y) :
      (d x y he).Pstar = graphLocalGroup F x :=
    graphActorLocalData_star ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hm x y he
  have hvw : v ≠ w := by
    intro hh
    have hdist := hc.1
    have hp := source_b_positive ht
    rw [hh,SimpleGraph.dist_self] at hdist
    omega
  obtain ⟨a,hva,_⟩ := exists_predecessor F ht.generate w v hvw.symm
  obtain ⟨z,hwz,_⟩ := exists_predecessor F ht.generate v w hvw
  exact reduced_critical_core_indices_eq_of_localData h hc hne _ _ (d v a hva) (d w z hwz)
    (by rw [hd]; exact graph_actor_odd_index ht v)
    (by rw [hd]; exact graph_actor_odd_index ht w)

/-- Every SL₂ marking with the original kernel has field order equal to the opposite-center index. -/
theorem reduced_critical_field_order_eq_index (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (π : graphLocalGroup F v →* SL(2,k)) (hπ : Function.Surjective π)
    (hk : π.ker = (Q F v).subgroupOf (graphLocalGroup F v)) :
    Nat.card k = (Q F v).relIndex (Z F w) := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let d := graphActorLocalData ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hm
  have hd := graphActorLocalData_star ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hm
  have hn := reduced_critical_natural_centers_of_localData h (graphLocalGroup F) d hd
    (graph_actor_odd_index ht) hc hne
  let := graph_Z_elementary ht w
  let : IsElementaryAbelian 2 (Z F w) := graph_Z_elementary ht w
  exact field_card_of_sylow_product (stabilizer F v) (graphLocalGroup F v) (Q F v) (Z F w)
    (sylowGenerated_le _)
    (pGroup_le_sylowGenerated _ _ (pCoreIn_le 2 _) (isPGroup_pCoreIn 2 _))
    (pGroup_le_sylowGenerated _ _ (criticalPair_centers F ht.generate hc).1
      (IsElementaryAbelian.isPGroup 2 _)) hn.2.2.1 π hπ hk

/-- The actual fields in any two critical quotient markings have the same order, in either orientation. -/
theorem reduced_critical_marked_field_orders (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    {k₀ k₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    (π₀ : graphLocalGroup F v →* SL(2,k₀)) (hπ₀ : Function.Surjective π₀)
    (hk₀ : π₀.ker = (Q F v).subgroupOf (graphLocalGroup F v))
    (π₁ : graphLocalGroup F w →* SL(2,k₁)) (hπ₁ : Function.Surjective π₁)
    (hk₁ : π₁.ker = (Q F w).subgroupOf (graphLocalGroup F w)) :
    Nat.card k₀ = Nat.card k₁ := by
  have hc' := (reduced_noncommuting_critical_intersections h hc hne).1
  exact (reduced_critical_field_order_eq_index h hm hc hne π₀ hπ₀ hk₀).trans
    ((reduced_critical_core_indices_eq h hm hc hne).trans
      (reduced_critical_field_order_eq_index h hm hc' (by rwa [commutator_comm]) π₁ hπ₁ hk₁).symm)

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
