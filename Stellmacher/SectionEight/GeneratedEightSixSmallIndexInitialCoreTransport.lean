module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexInitialReduction
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexCenter
public import Stellmacher.SectionFiveToSeven.Result7_1

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u v

public theorem eight_six_neighbor_core_intersection_equiv
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex)
    (hprevious : previous ∈ Later.Neighborhood graph path.a) :
    Nonempty ((VAt graph previous ⊓ QAt graph path.a : Subgroup G) ≃*
      (VAt graph path.firstStep ⊓ QAt graph path.a : Subgroup G)) := by
  have hneighbor : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  obtain ⟨actor, hactor⟩ :=
    (lemma_seven_one hyp graph).local_transitivity path.a hneighbor hprevious
  let equiv := MulAut.conj (actor : G)⁻¹
  have hQmap : (QAt graph path.a).map equiv.toMonoidHom = QAt graph path.a :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (QAt graph path.a : Set G)).inv_mem
        (SevenSix.stabilizer_le_normalizer_q graph path.a actor.property))
  have hVmap : (VAt graph path.firstStep).map equiv.toMonoidHom =
      VAt graph previous := by
    rw [← hactor]
    exact (v_act graph actor path.firstStep).symm
  have hintersection : (VAt graph path.firstStep ⊓ QAt graph path.a).map
      equiv.toMonoidHom = VAt graph previous ⊓ QAt graph path.a := by
    rw [Subgroup.map_inf _ _ _ equiv.injective, hVmap, hQmap]
  exact ⟨(MulEquiv.subgroupCongr hintersection.symm).trans
    (equiv.subgroupMap (VAt graph path.firstStep ⊓ QAt graph path.a)).symm⟩

public theorem eight_six_predecessor_intersection_model
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex)
    (hprevious : previous ∈ Later.Neighborhood graph path.a)
    (next : EightSixSmallIndexNextData graph path) :
    IsModel (VAt graph previous ⊓ QAt graph path.a) (C2 × C4) := by
  obtain ⟨transport⟩ := eight_six_neighbor_core_intersection_equiv
    hyp graph path previous hprevious
  obtain ⟨model⟩ := next.intersection
  exact ⟨transport.trans model⟩

public theorem eight_six_initial_intersection_cards
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex)
    (hprevious : previous ∈ Later.Neighborhood graph path.a)
    (D : Subgroup G)
    (hindex : QuotientCardEq (VAt graph previous ⊓ QAt graph path.a)
      ((VAt graph previous ⊓ QAt graph path.a) ⊓ D) 2)
    (next : EightSixSmallIndexNextData graph path) :
    Nat.card (VAt graph previous ⊓ QAt graph path.a : Subgroup G) = 8 ∧
      Nat.card (VAt graph path.firstStep ⊓ QAt graph path.a : Subgroup G) = 8 ∧
      Nat.card ((VAt graph previous ⊓ QAt graph path.a) ⊓ D : Subgroup G) = 4 := by
  obtain ⟨previousModel⟩ := eight_six_predecessor_intersection_model
    hyp graph path previous hprevious next
  obtain ⟨firstModel⟩ := next.intersection
  have hcard : Nat.card (C2 × C4) = 8 := by
    simp [C2, C4, Nat.card_eq_fintype_card]
  have hpreviousCard := (Nat.card_congr previousModel.toEquiv).trans hcard
  have hfirstCard := (Nat.card_congr firstModel.toEquiv).trans hcard
  refine ⟨hpreviousCard, hfirstCard, ?_⟩
  change Nat.card (VAt graph previous ⊓ QAt graph path.a : Subgroup G) =
    2 * Nat.card ((VAt graph previous ⊓ QAt graph path.a) ⊓ D : Subgroup G) at hindex
  omega

end Stellmacher.SectionEight
