module

public import Stellmacher.SectionEight.GeneratedEightSixIntersectionCommutator
public import Stellmacher.SectionEight.GeneratedEightSixCentralizerIndexTwo
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_two_subgroup_core_part_index_dvd_two
    {G : Type u} [Group G] [Finite G]
    (P Q V : Subgroup G) (hVP : V ≤ P) (hV : IsPGroup 2 V)
    (hquot : QuotientIsModel P Q SL2Two) :
    (V ⊓ Q).relIndex V ∣ 2 := by
  obtain ⟨projection, _, hkernel⟩ := hquot
  let restricted : V →* SL2Two := projection.comp (Subgroup.inclusion hVP)
  have hker : restricted.ker = (V ⊓ Q).subgroupOf V := by
    ext element
    change projection (Subgroup.inclusion hVP element) = 1 ↔
      (element : G) ∈ V ∧ (element : G) ∈ Q
    rw [← MonoidHom.mem_ker, hkernel]
    exact ⟨fun helement => ⟨element.property, helement⟩, fun helement => helement.2⟩
  have hRp : IsPGroup 2 restricted.range :=
    hV.of_surjective restricted.rangeRestrict restricted.rangeRestrict_surjective
  have hcard : Nat.card restricted.range ∣ 6 := by
    rw [← SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
      (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)]
    exact Subgroup.card_subgroup_dvd_card _
  have hcoprime : Nat.Coprime (Nat.card restricted.range) 3 := by
    obtain ⟨exponent, hexponent⟩ := hRp.exists_card_eq
    rw [hexponent]
    exact (by decide : Nat.Coprime 2 3).pow_left exponent
  change ((V ⊓ Q).subgroupOf V).index ∣ 2
  rw [← hker, Subgroup.index_ker]
  exact hcoprime.dvd_of_dvd_mul_right hcard

public theorem eight_six_first_center_card_le_two
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (hcard : Nat.card (ZAt graph path.a) = 4) :
    Nat.card (ZAt graph path.firstStep) ≤ 2 := by
  have hle := eight_six_first_center_le_initial hyp graph path hcenter
  have hneq : ZAt graph path.firstStep ≠ ZAt graph path.a := by
    intro heq
    have hinitial : GAt graph path.a ≤
        Subgroup.normalizer (ZAt graph path.firstStep : Set G) :=
      heq ▸ stabilizer_le_normalizer_z graph path.a
    have hfirst : GAt graph path.firstStep ≤
        Subgroup.normalizer (ZAt graph path.firstStep : Set G) :=
      stabilizer_le_normalizer_z graph path.firstStep
    have hgen : GAt graph path.a ⊔ GAt graph path.firstStep = ⊤ := by
      rcases path.edge_stabilizers_are_P with hedge | hedge
      · exact (congrArg₂ (· ⊔ ·) hedge.1 hedge.2).trans hyp.generated
      · exact (congrArg₂ (· ⊔ ·) hedge.1 hedge.2).trans
          (sup_comm P2 P1 |>.trans hyp.generated)
    have hnormal : (ZAt graph path.firstStep).Normal := Subgroup.normalizer_eq_top_iff.mp
      (top_unique (hgen ▸ sup_le hinitial hfirst))
    have hZp : IsPGroup 2 (ZAt graph path.firstStep) := by
      let _ := SevenSix.z_isElementaryAbelian_of_neighbor hyp graph
        ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr
          (graph.adjacent_symm path.firstStep_adj))
      exact IsElementaryAbelian.isPGroup 2 _
    have hbot : ZAt graph path.firstStep = ⊥ :=
      le_bot_iff.mp ((show ZAt graph path.firstStep ≤ pCore 2 G from
        le_sSup ⟨hnormal, hZp⟩).trans_eq hyp.twoCore_eq_bot)
    rw [← heq, hbot, Subgroup.card_bot] at hcard
    omega
  have hdvd : Nat.card (ZAt graph path.firstStep) ∣ 4 :=
    hcard ▸ Subgroup.card_dvd_of_le hle
  have hcardneq : Nat.card (ZAt graph path.firstStep) ≠ 4 := by
    intro heq
    exact hneq (Subgroup.eq_of_le_of_card_ge hle (by omega))
  have hcases := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card (ZAt graph path.firstStep) ∣ 2 ^ 2 from hdvd)
  obtain ⟨exponent, hexponent, hpower⟩ := hcases
  have hcases : exponent = 0 ∨ exponent = 1 ∨ exponent = 2 := by omega
  rcases hcases with heq | heq | heq
  · rw [heq] at hpower
    exact hpower.le.trans (by decide)
  · rw [heq] at hpower
    exact hpower.le
  · exact (hcardneq (by simpa [heq] using hpower)).elim

public theorem eight_six_initial_center_le_core_part_centralizer
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q U : Subgroup G)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hU : U ≤ QAt graph path.a) :
    ZAt graph path.a ≤ D ⊓ Subgroup.centralizer (U : Set G) := by
  have hDN : GAt graph path.a ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
      data.intersection_normal.2
  have hZaD : ZAt graph path.a ≤ D := by
    rw [← data.residual_commutator]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (((SevenSix.twoResidualIn_le L).trans data.closure_le).trans hDN)
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  exact le_inf hZaD
    (((lemma_seven_three hyp graph).center_core path.a path.firstStep hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        ((SevenSix.centerAmbient_le_centralizer _).trans (Subgroup.centralizer_le hU))))

public theorem eight_six_first_core_part_centralizer_of_intersection_centralizer
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (hquot : QuotientIsModel (GAt graph path.a) (QAt graph path.a) SL2Two)
    (hcard : Nat.card (ZAt graph path.a) = 4)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hfull : D ⊓ Subgroup.centralizer (VAt graph path.firstStep : Set G) =
      ZAt graph path.firstStep) :
    D ⊓ Subgroup.centralizer
      (VAt graph path.firstStep ⊓ QAt graph path.a : Set G) = ZAt graph path.a := by
  have hsylow := SevenSix.edge_sylow_data hyp graph path
  have hVS : VAt graph path.firstStep ≤ S :=
    (le_sup_left.trans data.sylow_intersection.symm.le).trans inf_le_right
  have hS : IsPGroup 2 S := by
    obtain ⟨_, sylow, heq⟩ := hsylow.1
    rw [← heq]
    exact sylow.isPGroup'.map _
  have hindex := eight_six_two_subgroup_core_part_index_dvd_two
    (GAt graph path.a) (QAt graph path.a) (VAt graph path.firstStep)
    (hVS.trans hsylow.1.1) (hS.to_le hVS) hquot
  have hDQ : D ≤ QAt graph path.firstStep := hD ▸ inf_le_right
  have hQG : QAt graph path.firstStep ≤ GAt graph path.firstStep := by
    change graph.twoCoreAt path.firstStep ≤ _
    rw [graph.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor hyp graph
    ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr
      (graph.adjacent_symm path.firstStep_adj))
  have hbound := eight_six_index_two_centralizer_card D (VAt graph path.firstStep)
    (VAt graph path.firstStep ⊓ QAt graph path.a) (ZAt graph path.firstStep)
    inf_le_left hindex
    ((hcenter.trans (SevenSix.centerAmbient_le_centralizer _)).trans
      (Subgroup.centralizer_le (hDQ.trans hQG)))
    (by rw [Subgroup.commutator_comm];
        exact (Subgroup.commutator_mono le_rfl hDQ).trans_eq data.first_commutator) hfull
  have hsmall := eight_six_first_center_card_le_two hyp graph path hcenter hcard
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge
    (eight_six_initial_center_le_core_part_centralizer hyp graph path previous D L Q _
      data inf_le_right)
  rw [hcard]
  exact hbound.trans (by nlinarith)

private theorem map_inf_centralizer_equiv
    {G : Type u} [Group G] (D A : Subgroup G) (equiv : G ≃* G) :
    (D ⊓ Subgroup.centralizer (A : Set G)).map equiv.toMonoidHom =
      D.map equiv.toMonoidHom ⊓
        Subgroup.centralizer (A.map equiv.toMonoidHom : Set G) := by
  ext element
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hD, hcentral⟩
    refine ⟨hD, ?_⟩
    intro other hother
    simpa using congrArg equiv
      (hcentral (equiv.symm other) (Subgroup.mem_map_equiv.mp hother))
  · rintro ⟨hD, hcentral⟩
    refine ⟨hD, ?_⟩
    intro other hother
    apply equiv.injective
    simpa using hcentral (equiv other) (by simpa using hother)

public theorem eight_six_predecessor_core_part_centralizer_of_first_core_part
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (hprevious : previous ∈ Later.Neighborhood graph path.a)
    (D L Q : Subgroup G)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hfirst : D ⊓ Subgroup.centralizer
      (VAt graph path.firstStep ⊓ QAt graph path.a : Set G) = ZAt graph path.a) :
    D ⊓ Subgroup.centralizer
      (VAt graph previous ⊓ QAt graph path.a : Set G) = ZAt graph path.a := by
  have hneighbor : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  obtain ⟨actor, hactor⟩ :=
    (lemma_seven_one hyp graph).local_transitivity path.a hneighbor hprevious
  let equiv := MulAut.conj (actor : G)⁻¹
  have hDN : GAt graph path.a ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
      data.intersection_normal.2
  have hDmap : D.map equiv.toMonoidHom = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (D : Set G)).inv_mem (hDN actor.property))
  have hQmap : (QAt graph path.a).map equiv.toMonoidHom = QAt graph path.a :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (QAt graph path.a : Set G)).inv_mem
        (SevenSix.stabilizer_le_normalizer_q graph path.a actor.property))
  have hZmap : (ZAt graph path.a).map equiv.toMonoidHom = ZAt graph path.a :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (ZAt graph path.a : Set G)).inv_mem
        (stabilizer_le_normalizer_z graph path.a actor.property))
  have hVmap : (VAt graph path.firstStep).map equiv.toMonoidHom = VAt graph previous := by
    rw [← hactor]
    exact (v_act graph actor path.firstStep).symm
  have hmapped := congrArg (fun subgroup : Subgroup G => subgroup.map equiv.toMonoidHom) hfirst
  change (D ⊓ Subgroup.centralizer
    ((VAt graph path.firstStep ⊓ QAt graph path.a : Subgroup G) : Set G)).map
      equiv.toMonoidHom = _ at hmapped
  rw [map_inf_centralizer_equiv, Subgroup.map_inf _ _ _ equiv.injective,
    hDmap, hQmap, hZmap, hVmap] at hmapped
  exact hmapped

end Stellmacher.SectionEight
