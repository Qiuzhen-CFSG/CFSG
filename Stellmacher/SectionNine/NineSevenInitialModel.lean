module
public import Stellmacher.SectionNine.NineSevenBackwardIndex
public import Stellmacher.SectionNine.NineSevenModelInputs
public import Stellmacher.SectionNine.NineSevenCommutatorActionBridge
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs
public import Stellmacher.SectionNine.LemmaNineFive
public import Theory.GroupAction.InvolutionCentralizingCoatom

/-!
# The order-eight and quotient-model reduction in Stellmacher (9.7)

The original index-two intersection hypothesis forces the first-step module
to have order eight and its local core quotient to be SL₂(2). The ambient
Hypothesis Two carrier and exact third path offset are retained.

Cubic two-arc transport gives an index-two terminal/backward intersection.
Criticality supplies a first-step involution outside the terminal core; the
backward module commutes with this actor, so it fixes the intersection.
Involution rank-nullity bounds the displacement by two, and the faithful
terminal quotient criterion makes its order exactly two modulo the center.
The proved (9.5) dichotomy applies. Its order-thirty-two alternative would
have backward intersection of order eight, contradicting the transported
index two. Endpoint conjugation transfers the order-eight alternative and
its quotient model to the first step.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.7), printed p.53,
the initial paragraph, in `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_seven_initial_model
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2) :
    Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2 ^ 3 ∧
      QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
        (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let previous := cp.path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hprevious : IsCriticalPathOffset Γ cp (cp.length - 2) previous :=
    ⟨⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩, rfl, rfl⟩
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let K := U ⊓ VAt Γ previous
  have hbackIndex : QuotientCardEq U K 2 :=
    nine_seven_backward_index_two ctx hb third hpath hindex previous hprevious
  obtain ⟨actor, hactorFirst, hactorNot, hactorInv⟩ := nine_seven_exists_actor ctx.toLocalContext hb
  let R := ⁅U, Subgroup.zpowers actor⁆
  have hactorP : actor ∈ GAt Γ cp.a' :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2 hactorFirst
  have hcyclic : Subgroup.zpowers actor ≤ GAt Γ cp.a' := Subgroup.zpowers_le.mpr hactorP
  have hnormal : Subgroup.zpowers actor ≤ Subgroup.normalizer (U : Set G) :=
    hcyclic.trans (stabilizer_le_normalizer_v Γ cp.a')
  have hfixed : K ≤ Subgroup.centralizer (Subgroup.zpowers actor : Set G) :=
    (show K ≤ VAt Γ previous from inf_le_right).trans
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (nine_five_previous_module_commutes_first ctx.toLocalContext hb previous hprevious)).trans
        (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hactorFirst)))
  let _ : IsElementaryAbelian 2 U :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.2.1
  have hRbound : Nat.card R ≤ 2 :=
    Subgroup.commutator_card_le_two_of_centralizing_index_two
      U K actor hactorInv hnormal inf_le_left hbackIndex hfixed
  obtain ⟨alignment, _, halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have horbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨alignment, halign⟩
  obtain ⟨hZcard, hmoduleCore, hkernel⟩ :=
    nine_next_center_commutator_and_kernel ctx hb cp.a' horbit
  have hRnot : ¬ R ≤ Z := fun hle => hactorNot ((hkernel actor hactorP).mp hle)
  have hRne : R ≠ ⊥ := fun heq => hRnot (heq ▸ bot_le)
  have hRcard : Nat.card R = 2 := by
    have hpos := (Subgroup.one_lt_card_iff_ne_bot R).mpr hRne
    omega
  have hRZ : R ⊓ Z = ⊥ := by
    by_contra hne
    have hpos := (Subgroup.one_lt_card_iff_ne_bot (R ⊓ Z)).mpr hne
    have hequal : R ⊓ Z = R := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact hRnot (hequal ▸ inf_le_right)
  have hRU : R ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hnormal
  have hQP : QAt Γ cp.a' ≤ GAt Γ cp.a' := by
    rw [QAt, q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZU : Z ≤ U := by
    change ZAt ctx.Γ cp.a' ≤ U
    rw [← hmoduleCore]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQP.trans (stabilizer_le_normalizer_v Γ cp.a'))
  have hab : U ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hnormalize : R ≤ Subgroup.normalizer (Z : Set G) :=
    hRU.trans (hab.trans ((Subgroup.centralizer_le hZU).trans
      (Subgroup.centralizer_le_normalizer _)))
  have hcommIndex : QuotientCardEq (R ⊔ Z) Z 2 := by
    have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes Z R hnormalize
    rw [inf_comm, hRZ, Subgroup.card_bot, hRcard, one_mul, sup_comm] at hcard
    change Nat.card (R ⊔ Z : Subgroup G) = 2 * Nat.card Z
    rw [← hcard, Nat.mul_comm]
  have hindexNative : (K.subgroupOf U).index = 2 := by
    have hproduct := (K.subgroupOf U).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show K ≤ U from inf_le_left)).toEquiv] at hproduct
    have hpos := Nat.card_pos (α := K)
    change Nat.card U = 2 * Nat.card K at hbackIndex
    nlinarith
  have hcontain : R ≤ VAt Γ previous :=
    (nine_seven_normalized_index_two_commutator_le U K (Subgroup.zpowers actor)
      hindexNative hnormal
      ((Subgroup.le_centralizer_iff.mp hfixed).trans
        (Subgroup.centralizer_le_normalizer _))).trans inf_le_right
  have hsmall : Nat.card U = 2^3 ∧ QuotientIsModel (GAt Γ cp.a') (QAt Γ cp.a') SL2Two := by
    rcases lemma_nine_five_ambient ctx hb previous hprevious actor
      ⟨hactorFirst, hactorNot⟩ hcommIndex hcontain with hsmall | hlarge
    · exact hsmall
    · obtain ⟨hlarge, _, hintersection⟩ := hlarge
      change Nat.card U = 2 * Nat.card K at hbackIndex
      change Nat.card U = 2^5 at hlarge
      change Nat.card K = 2^3 at hintersection
      norm_num [hlarge, hintersection] at hbackIndex
  exact ⟨(nine_seven_endpoint_module_card ctx.toLocalContext).trans hsmall.1,
    (nine_seven_endpoint_quotient_model_iff ctx.toLocalContext).mpr hsmall.2⟩

end Stellmacher.SectionNine
