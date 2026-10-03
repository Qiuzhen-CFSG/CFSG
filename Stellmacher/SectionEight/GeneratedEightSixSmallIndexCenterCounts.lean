module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexCountsTools
public import Stellmacher.SectionEight.GeneratedEightSixCorePartCentralizers

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_predecessor_commutator_and_center_bound
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (hcard : Nat.card (ZAt graph path.a) = 4)
    (previous : graph.Vertex) (hprevious : previous ∈ Later.Neighborhood graph path.a)
    (D L Q : Subgroup G)
    (data : EightSixEquationOneData graph path previous D L Q) :
    ⁅QAt graph previous, VAt graph previous⁆ = ZAt graph previous ∧
      Nat.card (ZAt graph previous) ≤ 2 := by
  have hneighbor : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  obtain ⟨actor, hactor⟩ :=
    (lemma_seven_one hyp graph).local_transitivity path.a hneighbor hprevious
  let equiv := MulAut.conj (actor : G)⁻¹
  have hQmap : (QAt graph path.firstStep).map equiv.toMonoidHom =
      QAt graph previous := by
    rw [← hactor]
    exact (SevenSix.q_act graph actor path.firstStep).symm
  have hVmap : (VAt graph path.firstStep).map equiv.toMonoidHom =
      VAt graph previous := by
    rw [← hactor]
    exact (v_act graph actor path.firstStep).symm
  have hZmap : (ZAt graph path.firstStep).map equiv.toMonoidHom =
      ZAt graph previous := by
    rw [← hactor]
    exact (z_act graph actor path.firstStep).symm
  constructor
  · have hmapped := congrArg (fun subgroup : Subgroup G =>
        subgroup.map equiv.toMonoidHom) data.first_commutator
    rw [Subgroup.map_commutator, hVmap, hQmap, hZmap,
      Subgroup.commutator_comm] at hmapped
    exact hmapped
  · rw [← hZmap, Subgroup.card_map_of_injective equiv.injective]
    exact eight_six_first_center_card_le_two hyp graph path hcenter hcard

public theorem eight_six_small_index_center_counts
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (hcard : Nat.card (ZAt graph path.a) = 4)
    (previous : graph.Vertex) (hprevious : previous ∈ Later.Neighborhood graph path.a)
    (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt graph previous ⊓ QAt graph path.a)
      ((VAt graph previous ⊓ QAt graph path.a) ⊓ D) 2)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hcentralizer : D ⊓ Subgroup.centralizer
      (VAt graph previous ⊓ QAt graph path.a : Set G) = ZAt graph path.a) :
    QuotientCardEq D (ZAt graph path.a) 1 ∨
      QuotientCardEq D (ZAt graph path.a) 2 := by
  let _ : IsElementaryAbelian 2 D := helementary
  have hneighbor : path.a ∈ neighborhood graph previous :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
      (graph.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent graph).mp hprevious))
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor hyp graph hneighbor
  have hDprevious : D ≤ QAt graph previous := hD ▸ inf_le_left
  have hZcentral : ZAt graph previous ≤ Subgroup.centralizer (D : Set G) :=
    ((lemma_seven_three hyp graph).center_core previous path.a hneighbor).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        ((SevenSix.centerAmbient_le_centralizer _).trans
          (Subgroup.centralizer_le hDprevious)))
  obtain ⟨hcommutator, hsmall⟩ := eight_six_predecessor_commutator_and_center_bound
    hyp graph path hcenter hcard previous hprevious D L Q data
  have hbound := eight_six_abelian_index_two_centralizer_bound
    D (VAt graph previous ⊓ QAt graph path.a) (ZAt graph previous)
    (dvd_of_eq (eight_six_relIndex_two_of_quotient_card _ _ inf_le_left hindex))
    hZcentral ((Subgroup.commutator_mono hDprevious inf_le_left).trans_eq hcommutator)
  change D ⊓ Subgroup.centralizer
    ((VAt graph previous ⊓ QAt graph path.a : Subgroup G) : Set G) =
      ZAt graph path.a at hcentralizer
  rw [hcentralizer] at hbound
  exact eight_six_quotient_card_one_or_two_of_bound D (ZAt graph path.a)
    (hcentralizer ▸ inf_le_left)
    (hbound.trans (by nlinarith))

end Stellmacher.SectionEight
