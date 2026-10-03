module
public import Stellmacher.SectionFiveToSeven.SixFourBarredAction
public import Stellmacher.SectionOne.QuadraticIndexTwoCriticalFixed
public import Stellmacher.SectionFiveToSeven.Result5_3
public import Stellmacher.SectionTwo.QuotientModuleTransport
public import Stellmacher.SectionTwo.LemmaTwoOne
public import Stellmacher.SectionTwo.VSubgroupElementaryAbelian

/-!
# Quadratic index-two actions fix the canonical barred critical subgroup

Under Hypothesis Two, suppose Q lies in S and its action on the actual
Section Six module V has full fixed index two and is quadratic. Then the
canonical barred critical subgroup J is nontrivial, and [V,Q] centralizes
its full preimage in the original ambient group.

Retain the named canonical quotient action on the intrinsic Section Two
module. Injective subtype maps identify its image-actor fixed subgroup and
commutator with the given ambient fixed subgroup and [V,Q]. The quadratic
index-two theorem makes this actor a nontrivial offender. By (1.7)(b), J
is elementary abelian and fixes its displacement images of order at most
two. The canonical fixed-point equivalence then gives centralization of
the entire preimage, including the kernel.

This supplies the precise fixed-vector hypothesis for the application of
(6.4) in (9.2), without replacing that hypothesis by Baumann centralization.
Source: Stellmacher, Journal of Algebra 190 (1997), (1.7), (6.4), and (9.2),
printed p.48 / PDF p.38 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u
private theorem map_inf_centralizer
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (A K : Subgroup G) :
    (A ⊓ Subgroup.centralizer (K : Set G)).map f =
      A.map f ⊓ Subgroup.centralizer (K.map f : Set H) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f ha.1, ?_⟩
    change f a ∈ Subgroup.centralizer (K.map f : Set H)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    simpa only [map_mul] using congrArg f (Subgroup.mem_centralizer_iff.mp ha.2 k hk)
  · rintro _ ⟨⟨a, ha, rfl⟩, hcent⟩
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    change a ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    apply hf
    simpa only [map_mul] using
      Subgroup.mem_centralizer_iff.mp hcent (f k) (Subgroup.mem_map_of_mem f hk)


private theorem quotient_commutator_image_map
    {G X : Type u} [Group G] [Group X]
    (T : Sylow 2 G) (q : G →* X) (hq : Function.Surjective q)
    (hker : q.ker = SectionTwo.cSubgroup T) (A : Subgroup G) :
    letI := SectionTwo.quotientConjugationAction T q hq hker
    (commutatorAction (A.map q) (SectionTwo.vSubgroup T)).map
      (SectionTwo.vSubgroup T).subtype = ⁅SectionTwo.vSubgroup T,A⁆ := by
  let V := SectionTwo.vSubgroup T
  let _ := SectionTwo.quotientConjugationAction T q hq hker
  let _ : V.Normal := Subgroup.normalClosure_normal
  have hnorm : A ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer_of_normal
  let _ : Subgroup.Normalizes A V := ⟨hnorm⟩
  have heq : commutatorAction (A.map q) V = commutatorAction A V := by
    rw [commutatorAction_eq_closure,commutatorAction_eq_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨actor,v,rfl⟩
      obtain ⟨a,ha,he⟩ := actor.property
      refine ⟨⟨a,ha⟩,v,?_⟩
      congr 1
      apply Subtype.ext
      change ((actor.val • v : V) : G) = a * (v : G) * a⁻¹
      rw [← he,SectionTwo.quotientConjugationAction_smul_coe T q hq hker]
    · rintro ⟨actor,v,rfl⟩
      refine ⟨⟨q actor,Subgroup.mem_map_of_mem q actor.property⟩,v,?_⟩
      congr 1
      apply Subtype.ext
      change (actor : G) * (v : G) * (actor : G)⁻¹ = ((q actor • v : V) : G)
      rw [SectionTwo.quotientConjugationAction_smul_coe T q hq hker]
  rw [heq,commutatorAction_subgroup_conj_map_eq_commutator V A hnorm]

public theorem sixFour_quadratic_index_two_barred_fixed
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (Q : Subgroup H) (hQS : Q ≤ S)
    (hindex : Nat.card (sectionSixV S P1) =
      2 * Nat.card (sectionSixV S P1 ⊓ Subgroup.centralizer (Q : Set H) : Subgroup H))
    (hquad : ⁅⁅sectionSixV S P1,Q⁆,Q⁆ = ⊥) :
    sectionSixBarredCritical h ≠ ⊥ ∧
      ⁅sectionSixV S P1,Q⁆ ≤
        Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H) := by
  classical
  let SP := sectionSixSylow h
  let V := sectionSixLocalV h
  let q := sectionSixQuotientMap h
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective (sectionSixLocalC h)
  have hker : q.ker = SectionTwo.cSubgroup SP := QuotientGroup.ker_mk' _
  let _ := sectionSixQuotientAction h
  let f : V →* H := P1.subtype.comp V.subtype
  have hf : Function.Injective f := P1.subtype_injective.comp V.subtype_injective
  have hsetup := sectionSix_barred_action_setup h
  have hVP1 : V.map P1.subtype = sectionSixV S P1 := hsetup.localV_image
  have hSP : (SP : Subgroup P1).map P1.subtype = S := hsetup.sylow_image
  have hQP : Q ≤ P1 := hQS.trans h.fiveOne.P1_mem.1.2.1.1
  let Q1 := Q.subgroupOf P1
  have hQ1 : Q1.map P1.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQP
  let Y := Q1.map q
  let U := sectionSixBarSylow h
  have hQU : Y ≤ (U : Subgroup (SectionSixBarP1 h)) := by
    apply Subgroup.map_mono
    apply (Subgroup.map_le_map_iff_of_injective P1.subtype_injective).mp
    rw [hQ1,hSP]
    exact hQS
  have hfixedMap : (FixedPoints.subgroup Y V).map f =
      sectionSixV S P1 ⊓ Subgroup.centralizer (Q : Set H) := by
    rw [show f = P1.subtype.comp V.subtype from rfl,← Subgroup.map_map]
    rw [SectionTwo.quotientConjugationAction_fixedPoints_image_map SP q hq hker Q1]
    rw [map_inf_centralizer P1.subtype P1.subtype_injective,hVP1,hQ1]
  have hcommMap : (commutatorAction Y V).map f = ⁅sectionSixV S P1,Q⁆ := by
    rw [show f = P1.subtype.comp V.subtype from rfl,← Subgroup.map_map]
    rw [quotient_commutator_image_map SP q hq hker Q1,Subgroup.map_commutator,hVP1,hQ1]
  have hVcard : Nat.card V = Nat.card (sectionSixV S P1) := by
    rw [← hVP1,Subgroup.card_map_of_injective P1.subtype_injective]
  have hfixedIndex : Nat.card V = 2 * Nat.card (FixedPoints.subgroup Y V) := by
    rw [hVcard,hindex,← hfixedMap,Subgroup.card_map_of_injective hf]
  have hquadFixed : commutatorAction Y V ≤ FixedPoints.subgroup Y V := by
    apply (Subgroup.map_le_map_iff_of_injective hf).mp
    rw [hfixedMap]
    refine le_inf ?_ ?_
    · rw [← hVP1,show f = P1.subtype.comp V.subtype from rfl,← Subgroup.map_map]
      exact Subgroup.map_mono (Subgroup.map_subtype_le _)
    · rw [hcommMap]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hquad
  obtain ⟨hsol,hchar,_⟩ := lemma_five_three S0 S P1 P2 h
  have hSPne : (SP : Subgroup P1) ≠ ⊥ := by
    intro hb
    apply h.fiveOne.S_nontrivial
    rw [← hSP,hb,Subgroup.map_bot]
  have hdvd : 2 ∣ Nat.card SP := SP.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hSPne (Subgroup.card_eq_one.mp hc))
  have hsec : SectionTwo.Hypotheses P1 :=
    ⟨hsol,even_iff_two_dvd.mpr (hdvd.trans (SP : Subgroup P1).card_subgroup_dvd_card),hchar⟩
  let _ : IsElementaryAbelian 2 V :=
    (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec SP).2
  have hUne : (U : Subgroup (SectionSixBarP1 h)) ≠ ⊥ := by
    intro hb
    have hY : Y = ⊥ := bot_unique (hb ▸ hQU)
    have hfix : FixedPoints.subgroup Y V = ⊤ := by
      ext v
      simp only [FixedPoints.mem_subgroup,Subgroup.mem_top,iff_true]
      intro actor
      have ha : (actor : SectionSixBarP1 h) = 1 := hY.le actor.property
      change (actor : SectionSixBarP1 h) • v = v
      rw [ha,one_smul]
    rw [hfix,Subgroup.card_top] at hfixedIndex
    have hp : 0 < Nat.card V := Nat.card_pos
    omega
  have hUdvd : 2 ∣ Nat.card U := U.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hUne (Subgroup.card_eq_one.mp hc))
  let _ : Group.IsSolvable P1 := hsol
  have hOne : SectionOne.Hypotheses (SectionSixBarP1 h) V :=
    ⟨Group.isSolvable_of_surjective hq,
      even_iff_two_dvd.mpr (hUdvd.trans (U : Subgroup (SectionSixBarP1 h)).card_subgroup_dvd_card),
      SectionTwo.quotientConjugationAction_faithful SP q hq hker,
      SectionTwo.lemma_two_one hsec SP q hq hker⟩
  obtain ⟨hJ,hfixed⟩ := SectionOne.oneJ_fixed_commutator_of_quadratic_index_two hOne U Y hQU hfixedIndex hquadFixed
  refine ⟨hJ,?_⟩
  rw [← hcommMap]
  rintro element ⟨vector,hvector,rfl⟩
  exact (hsetup.mem_fixedPoints_iff vector).mp (hfixed hvector)

end Stellmacher.SectionsFiveToSeven
