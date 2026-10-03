module
public import Stellmacher.SectionTen.TenOneLargeFirstResidualIndex
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# Middle-core action on the generated subgroup in source (16)

In the no-transvection Section Ten case, the middle two-core centralizes
W modulo the common endpoint-module intersection I. The actual context,
conjugate closure and subgroups are retained, and no source-(16) conclusion
or final large-case quotient model is assumed.

Source (15) identifies the first seed with its residual-core intersection,
which has order sixteen. Source (14) gives I order eight. The middle core
normalizes the seed and I, so it acts trivially on their order-two quotient.
In the middle stabilizer, both its two-core and I are normal; the
normal-closure commutator transfer extends this bound from the seed to W.

This is the middle-core input to the Y commutator estimate in Stellmacher
(10.1), Journal of Algebra 190 (1997), printed p.64, before equation (16).
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_generated_core_commutator
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    ⁅conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle),QAt ctx.Γ middle⁆ ≤
        VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' := by
  let P := GAt ctx.Γ middle
  let Q := QAt ctx.Γ middle
  let A := VAt ctx.Γ ctx.criticalPath.firstStep
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
  let seed := A ⊓ QAt ctx.Γ ctx.criticalPath.a'
  let I := A ⊓ V
  let W := conjugateClosure seed P
  obtain ⟨hres,hWU⟩ := ten_one_large_first_residual_index ctx middle hpath hno
  obtain ⟨_,hVcard,hIcard⟩ := ten_one_large_terminal_structure ctx middle hpath hno
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hlong : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hAcard : Nat.card A=32 := by
    obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
      middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal)
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
    change Nat.card (v ctx.Γ ctx.criticalPath.firstStep)=32
    rw [←hmove,v_act]
    exact (Nat.card_congr (V.equivMapOfInjective
      (MulAut.conj (mover:G)⁻¹).toMonoidHom (MulAut.conj (mover:G)⁻¹).injective).toEquiv).symm.trans hVcard
  have hUQend : U ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a') ≤ ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hseedW : seed ≤ W := by
    intro x hx
    exact Subgroup.subset_closure ⟨(1:P),⟨x,hx⟩,by simp⟩
  have hseedEq : seed=A⊓U := le_antisymm
    (le_inf inf_le_left (hseedW.trans hWU)) (inf_le_inf_left A hUQend)
  have hseedCard : Nat.card seed=16 := by
    change Nat.card A=2*Nat.card (A⊓U:Subgroup G) at hres
    rw [←hseedEq,hAcard] at hres
    omega
  have hIseed : I ≤ seed := inf_le_inf_left A
    (neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hshort _)
  have hindex : I.relIndex seed=2 := by
    have hh := (I.subgroupOf seed).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIseed).toEquiv,hIcard,hseedCard] at hh
    change I.relIndex seed*8=16 at hh
    omega
  have hQP : Q ≤ P := by
    change ctx.Γ.twoCoreAt middle ≤ P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hAQ : A ≤ Q :=
    (show A≤GeneratedNeighborhoodV ctx.Γ middle from
      le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst,rfl⟩).trans
      (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hlong middle)
  have hseedP : seed ≤ P := inf_le_left.trans (hAQ.trans hQP)
  have hIP : I ≤ P := inf_le_left.trans (hAQ.trans hQP)
  have hPI : P ≤ Subgroup.normalizer (I:Set G) := ten_one_common_intersection_normalized ctx middle hpath
  have hQseed : Q ≤ Subgroup.normalizer (seed:Set G) :=
    (le_inf
      ((((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2).trans
        (stabilizer_le_normalizer_v ctx.Γ _))
      ((((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal) default).2.2).trans
        (stabilizer_le_normalizer_q ctx.Γ _))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hseedComm := Subgroup.commutator_le_of_normalized_index_two
    seed I Q hIseed hindex hQseed (hQP.trans hPI)
  let _ : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr (stabilizer_le_normalizer_q ctx.Γ middle)
  let _ : (I.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hIP).mpr hPI
  have hinternal : ⁅Q.subgroupOf P,seed.subgroupOf P⁆ ≤ I.subgroupOf P := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hQP,
      Subgroup.map_subgroupOf_eq_of_le hseedP,Subgroup.map_subgroupOf_eq_of_le hIP,
      Subgroup.commutator_comm]
    exact hseedComm
  have hclosed := Subgroup.map_mono (f:=P.subtype)
    (Subgroup.commutator_normalClosure_le_of_normal
      (Q.subgroupOf P) (seed.subgroupOf P) (I.subgroupOf P) hinternal)
  rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hQP,
    Subgroup.map_subgroupOf_eq_of_le hIP] at hclosed
  rw [Subgroup.commutator_comm]
  exact (Subgroup.commutator_mono le_rfl
    (conjugateClosure_le_map_normalClosure seed P hseedP)).trans hclosed

end Stellmacher.SectionTen
