module
public import Stellmacher.SectionTen.TenOneLargeMutualCentralizers
public import Stellmacher.SectionTen.TenOneActorImageNontrivial
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupAction.SubgroupQuotientCommutatorBound

/-!
# Residual action on the terminal module centralizer

In the no-transvection Section Ten case, the terminal residual centralizes
C_Qend(Vend) modulo Vend. All groups are the actual graph subgroups, and no
later centralizer equality or Frobenius quotient is assumed.

An element of the middle stabilizer centralizing its order-four center fixes
all three distinct neighbor center lines, and therefore belongs to the cubic
action kernel. This places C_Qend(Vend) in the middle core. Its commutator
with the first module lies in their mutual centralizer intersection, hence
in Vend. The actual conjugation action on C_Qend(Vend)/Vend kills the first
module; the P-set kernel theorem then forces it to kill the terminal residual.
Lifting that same quotient action proves the asserted commutator bound.

This is the first transfer in the proof of Stellmacher (10.1)(16), Journal
of Algebra 190 (1997), printed p.64.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem middle_center_kernel
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    GAt ctx.Γ middle ⊓ Subgroup.centralizer (ZAt ctx.Γ middle:Set G) ≤ QAt ctx.Γ middle := by
  obtain ⟨horbit,_,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hopen := sectionTenOpeningData ctx middle hpath
  obtain ⟨hjoin,hcenters⟩ := nine_seven_center_join ctx.toAmbientSectionNineContext middle horbit
  obtain ⟨hlines,_,_⟩ := nine_seven_center_lines_of_center_join ctx.sectionSeven ctx.Γ
    middle hopen.quotient_model hopen.center_card hjoin hcenters
  have hcubic := cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle hopen.quotient_model
  rintro x ⟨hxP,hxC⟩
  apply (hcubic.kernel ⟨x,hxP⟩).mpr
  intro neighbor hadj
  by_contra hne
  have hfix : ctx.Γ.act x middle=middle :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def middle) _).mp hxP
  have hnew := adjacent_act ctx.Γ x hadj
  rw [hfix] at hnew
  obtain ⟨hlineCard,hlineLe⟩ := hlines neighbor ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
  have hxLine : x ∈ Subgroup.centralizer (ZAt ctx.Γ neighbor:Set G) :=
    Subgroup.centralizer_le hlineLe hxC
  have hmap : (ZAt ctx.Γ neighbor).map (MulAut.conj x⁻¹).toMonoidHom = ZAt ctx.Γ neighbor :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ ((Subgroup.centralizer (ZAt ctx.Γ neighbor:Set G)).inv_mem hxLine))
  have hcentereq : ZAt ctx.Γ (ctx.Γ.act x neighbor)=ZAt ctx.Γ neighbor := by
    change z ctx.Γ (ctx.Γ.act x neighbor)=z ctx.Γ neighbor
    rw [z_act]
    exact hmap
  exact (nine_seven_rank_two_neighbor_centers_distinct ctx.sectionSeven ctx.Γ
    hopen.quotient_model (hjoin ▸ hopen.center_card) hlineCard hadj hnew (Ne.symm hne)) hcentereq.symm

public theorem ten_one_large_centralizer_residual_commutator
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    ⁅QAt ctx.Γ ctx.criticalPath.a' ⊓
      Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.a':Set G),
      EAt ctx.Γ ctx.criticalPath.a'⁆ ≤ VAt ctx.Γ ctx.criticalPath.a' := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let A := VAt ctx.Γ ctx.criticalPath.firstStep
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let C := Q ⊓ Subgroup.centralizer (V:Set G)
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hQP : Q ≤ P := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a' ≤ P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hCP : C ≤ P := inf_le_left.trans hQP
  have hPV : P ≤ Subgroup.normalizer (V:Set G) := stabilizer_le_normalizer_v ctx.Γ _
  have hNC : Subgroup.normalizer (V:Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (V:Set G):Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hPC : P ≤ Subgroup.normalizer (C:Set G) :=
    (le_inf (stabilizer_le_normalizer_q ctx.Γ _) (hPV.trans hNC)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hCmid : C ≤ QAt ctx.Γ middle := by
    apply le_trans ?_ (middle_center_kernel ctx middle hpath)
    exact le_inf
      (inf_le_left.trans (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) default).2.2))
      (inf_le_right.trans (Subgroup.centralizer_le
        (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal))))
  have hCA : C ≤ Subgroup.normalizer (A:Set G) :=
    (hCmid.trans (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2)).trans
      (stabilizer_le_normalizer_v ctx.Γ _)
  have hAP : A ≤ P := (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2
  have hcommA : ⁅C,A⁆ ≤ V := by
    have hb : ⁅C,A⁆ ≤ A ⊓ Subgroup.centralizer (V:Set G) := le_inf
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hCA)
      ((Subgroup.le_normalizer_iff_commutator_le_left.mp (hAP.trans hPC)).trans inf_le_right)
    rw [(ten_one_large_mutual_centralizers ctx middle hpath hno).1] at hb
    exact hb.trans inf_le_right
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  let _ : IsElementaryAbelian 2 A :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hshort).1
  let _ : IsElementaryAbelian 2 V := by
    obtain ⟨actor,_,hmove⟩ := lemma_seven_five_endpoint_alignment
      ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
    change IsElementaryAbelian 2 (v ctx.Γ ctx.criticalPath.a')
    rw [←hmove,v_act]
    exact IsElementaryAbelian.map (MulAut.conj actor⁻¹).toMonoidHom
  have hVC : V ≤ C := le_inf
    (neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hshort _)
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hN : (V.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVC).mpr (hCP.trans hPV)
  let _ := hN
  obtain ⟨action,hformula⟩ := Subgroup.exists_quotient_conjugation_action P C V hPC hPV hN
  have hAker := Subgroup.quotient_conjugation_action_kills_commutator_layer
    P C V A hN hPC hcommA action hformula
  have hEker : E.subgroupOf P ≤ action.ker := by
    by_contra hn
    obtain ⟨actor,hactor,hout⟩ := SetLike.not_le_iff_exists.mp
      (sectionTenOpeningData ctx middle hpath).first_noncontainment
    let actorP : P := ⟨actor,hAP hactor⟩
    exact (ten_one_first_actor_image_ne_one ctx middle hpath actorP hactor hout action hn)
      (hAker hactor)
  have hEP : E ≤ P := by
    change ctx.Γ.twoResidualAt ctx.criticalPath.a' ≤ P
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hbound := Subgroup.quotient_conjugation_commutator_le_sup
    P C V C E ⊥ hPC hEP le_rfl action hformula (by
      intro actor hactor point _
      have hh : action actor=1 := hEker hactor
      simp only [hh,MulAut.one_apply,inv_mul_cancel,Subgroup.one_mem])
  simpa only [Subgroup.commutator_comm,bot_sup_eq] using hbound

end Stellmacher.SectionTen
