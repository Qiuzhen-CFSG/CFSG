module

public import Stellmacher.SectionNine.LemmaNineThree
public import Stellmacher.SectionNine.NineNextCenterCommutator
public import Stellmacher.SectionNine.CubicLocalAction
public import Theory.GroupAction.FourElementInvolutionLines
public import Stellmacher.OmegaOneCenterMap

/-!
# The core omega-center after Stellmacher (9.3)

At a vertex in the initial orbit of a commuting critical pair of distance
larger than one, the omega-one subgroup of the center of the local two-core
is exactly the vertex center. This supplies the omega-center identity used
in the opening of Section Ten, while retaining Hypothesis Two on the ambient
group and the actual embedded graph.

At the initial vertex, (9.3) gives a center of order four and an SL2(2)
quotient. The cubic edge calculation puts the two-core at index two in the
edge Sylow subgroup. By (7.5) and the next-center calculation, that Sylow's
omega-center has order two. Its quotient of order two acts on the elementary
omega-center of the core; fixed points embed in the Sylow omega-center.
The involution displacement identity therefore bounds the core omega-center
by four. The (7.3) containment of the vertex center gives equality, which
then transports by conjugation along the initial vertex orbit.

Source: Stellmacher, Journal of Algebra 190 (1997), the consequences after
(9.3), printed p.50, and the Section Ten opening, printed p.59, in
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem normalizer_le_normalizer_omegaCenter
    {G : Type u} [Group G] (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (omegaOneCenter Q : Set G) := by
  let K : Subgroup Q :=
    (omega₁ (G := Subgroup.center Q) (p := 2)).map (Subgroup.center Q).subtype
  let _ : (omega₁ (G := Subgroup.center Q) (p := 2)).Characteristic :=
    omega₁_characteristic (Subgroup.center Q)
  let _ : K.Characteristic := inferInstance
  exact BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic Q K

private theorem omega_card_le_four
    {G : Type u} [Group G] [Finite G] (T Q : Subgroup G)
    (hQT : Q ≤ T) (hTQ : T ≤ Subgroup.normalizer (Q : Set G))
    (hindex : (Q.subgroupOf T).index = 2)
    (hfixed : Nat.card (omegaOneCenter T) = 2)
    (hlarge : 4 ≤ Nat.card (omegaOneCenter Q)) :
    Nat.card (omegaOneCenter Q) ≤ 4 := by
  let W := omegaOneCenter Q
  change 4 ≤ Nat.card W at hlarge
  let _ : IsElementaryAbelian 2 W := omegaOneCenterAmbient_elementaryAbelian Q
  let _ : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
    hTQ.trans (normalizer_le_normalizer_omegaCenter Q)
  let action : T →* MulAut W := W.normalizerMonoidHom.comp (Subgroup.inclusion hTW)
  let N := Q.subgroupOf T
  let _ : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).mpr hTQ
  have hker : N ≤ action.ker := by
    intro actor hactor
    apply MonoidHom.mem_ker.mpr
    ext vector
    change (actor : G) * (vector : G) * (actor : G)⁻¹ = vector
    have hcomm := ((mem_omegaOneCenterAmbient_iff Q (vector : G)).mp vector.property).2.2
      (actor : G) hactor
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  let rho : (T ⧸ N) →* MulAut W := QuotientGroup.lift N action hker
  let _ : MulDistribMulAction (T ⧸ N) W := MulDistribMulAction.compHom W rho
  have hactorCard : Nat.card (T ⧸ N) = 2 := hindex
  have hfixedLe : (FixedPoints.subgroup (T ⧸ N) W).map W.subtype ≤
      omegaOneCenter T := by
    rintro vector ⟨v, hv, rfl⟩
    have hvdata := (mem_omegaOneCenterAmbient_iff Q (v : G)).mp v.property
    apply (mem_omegaOneCenterAmbient_iff T (v : G)).mpr
    refine ⟨hQT hvdata.1, hvdata.2.1, ?_⟩
    intro actor hactor
    have heq := congrArg (fun w : W => (w : G))
      (hv (QuotientGroup.mk' N ⟨actor, hactor⟩))
    change actor * (v : G) * actor⁻¹ = (v : G) at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq)
  have hfixedCard : Nat.card (FixedPoints.subgroup (T ⧸ N) W) ≤ 2 := by
    have hbound := Subgroup.card_le_of_le hfixedLe
    rw [Subgroup.card_map_of_injective W.subtype_injective, hfixed] at hbound
    exact hbound
  obtain ⟨actor, hne, _⟩ := (Nat.card_eq_two_iff' (1 : T ⧸ N)).mp hactorCard
  have hsquare : actor ^ 2 = 1 := by
    simpa only [hactorCard] using pow_card_eq_one' (x := actor)
  obtain ⟨hcard, hcomm⟩ :=
    card_two_action_fixed_commutator_card_data (U := W) actor ⟨hne, hsquare⟩ hactorCard
  have hcommCard := Subgroup.card_le_of_le hcomm
  change Nat.card W ≤ 4
  nlinarith

/-- Initial-orbit vertex centers exhaust the omega-center of their local two-core. -/
public theorem nine_three_core_omega_eq_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (middle : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.a middle) :
    omegaOneCenter (QAt ctx.Γ middle) = ZAt ctx.Γ middle := by
  have hmodel := lemma_nine_three_ambient ctx hb ctx.criticalPath.a
    ⟨1, ctx.Γ.act_one _⟩
  have hnext := nine_next_center_order_of_initial_four ctx.toLocalContext hmodel.2
  have hfixed : Nat.card (omegaOneCenter T) = 2 := by
    rw [show omegaOneCenter T = ZAt ctx.Γ ctx.criticalPath.firstStep from
      (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).next_center.1.symm]
    exact hnext
  have hQT : QAt ctx.Γ ctx.criticalPath.a ≤ T :=
    (local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  have hTQ : T ≤ Subgroup.normalizer (QAt ctx.Γ ctx.criticalPath.a : Set G) :=
    (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1.trans
      (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a)
  have hZQ : ZAt ctx.Γ ctx.criticalPath.a ≤
      omegaOneCenter (QAt ctx.Γ ctx.criticalPath.a) :=
    (lemma_seven_three ctx.sectionSeven ctx.Γ).center_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj)
  have hlarge : 4 ≤ Nat.card (omegaOneCenter (QAt ctx.Γ ctx.criticalPath.a)) := by
    rw [← hmodel.2]
    exact Subgroup.card_le_of_le hZQ
  have hedge := (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven
    ctx.criticalPath.a hmodel.1).edge_card ctx.criticalPath.firstStep ctx.criticalPath.firstStep_adj
  have hcard : Nat.card T ≤ 2 * Nat.card (QAt ctx.Γ ctx.criticalPath.a) := by
    have hle := Subgroup.card_le_of_le ctx.criticalPath.S_le_edge_stabilizers
    exact hle.trans_eq hedge
  have hindex : ((QAt ctx.Γ ctx.criticalPath.a).subgroupOf T).index = 2 := by
    have hprod := ((QAt ctx.Γ ctx.criticalPath.a).subgroupOf T).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT).toEquiv] at hprod
    have hpos := Nat.card_pos (α := QAt ctx.Γ ctx.criticalPath.a)
    have hle : ((QAt ctx.Γ ctx.criticalPath.a).subgroupOf T).index ≤ 2 := by nlinarith
    have hne : ((QAt ctx.Γ ctx.criticalPath.a).subgroupOf T).index ≠ 1 := by
      intro hone
      have htop := Subgroup.index_eq_one.mp hone
      have heq : QAt ctx.Γ ctx.criticalPath.a = T := by
        apply le_antisymm hQT
        intro x hx
        have : (⟨x, hx⟩ : T) ∈ (QAt ctx.Γ ctx.criticalPath.a).subgroupOf T := by
          rw [htop]
          trivial
        exact this
      rw [heq, hfixed] at hlarge
      omega
    have hindexPos := Nat.pos_of_ne_zero
      (Subgroup.FiniteIndex.index_ne_zero (H := (QAt ctx.Γ ctx.criticalPath.a).subgroupOf T))
    omega
  have hbound := omega_card_le_four T (QAt ctx.Γ ctx.criticalPath.a)
    hQT hTQ hindex hfixed hlarge
  have hbase : omegaOneCenter (QAt ctx.Γ ctx.criticalPath.a) = ZAt ctx.Γ ctx.criticalPath.a :=
    (Subgroup.eq_of_le_of_card_ge hZQ (by rw [hmodel.2]; exact hbound)).symm
  obtain ⟨actor, rfl⟩ := horbit
  change omegaOneCenter (q ctx.Γ (ctx.Γ.act actor ctx.criticalPath.a)) =
    z ctx.Γ (ctx.Γ.act actor ctx.criticalPath.a)
  rw [q_act, z_act]
  change omegaOneCenterAmbient ((q ctx.Γ ctx.criticalPath.a).map _) = _
  rw [omegaOneCenterAmbient_map_injective _ (MulAut.conj actor⁻¹).injective]
  exact congrArg (fun subgroup : Subgroup G => subgroup.map (MulAut.conj actor⁻¹).toMonoidHom) hbase

end Stellmacher.SectionNine
