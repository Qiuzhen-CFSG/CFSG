module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.Basic
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Inner.FiveRestrictions.Actors
import all CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Inner.FiveRestrictions.Actors
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FiveCenter
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Inner
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceGeneration
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound
/-!
# The original Higman--Sims source action has no FF offenders

The actual extraspecial five-subgroup forces displacement at least twenty
on its central five-element. Its literal commutator expression and divisibility
of quintic binary displacement by four force displacement at least twelve on
the noncentral five-generator. The two certified involution representatives
invert these five-elements, so every inner involution moves at least six
dimensions in every faithful binary representation.

The actual ambient two-rank is at most five. An elementary actor of rank at
least two contains an inner involution; a rank-one offender would, by the
five-conjugate generation theorem, force degree at most five. Both contradict
the preceding displacement bounds. No small-degree recognition is required.
The internal import of FiveActors reuses its literal word identities without
changing their visibility or exposing a new finite certificate.

Source: Aschbacher--Smith B.4.2 and K.4, printed pp.86 and 457; GM02,
Proposition5.1, specialized to FF modules on the original source group.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
open _root_.Sporadic.LeechRelated.HS
open FiveSubgroup Twenty.Inner
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem hs_center_codim (σ : Representation (ZMod 2) Carrier V)
    (hf : Function.Injective σ) : 20 ≤ fixedCodim σ (zpowers z) := by
  obtain ⟨a,ha,hd⟩ := AbsoluteWindow.finrank_eq_fixed_add_twenty_mul σ hf
  have hc := fixedCodim_add_finrank σ (zpowers z)
  rw [← FiveActors.z_generates_center] at hc
  change fixedCodim σ ((center subgroup).map subgroup.subtype) +
    AbsoluteWindow.fiveCenterFixedDimension σ = Module.finrank (ZMod 2) V at hc
  rw [← FiveActors.z_generates_center]
  omega

private theorem hs_x_codim (σ : Representation (ZMod 2) Carrier V)
    (hf : Function.Injective σ) : 12 ≤ fixedCodim σ (zpowers x) := by
  have hz := hs_center_codim σ hf
  have hb := fixedCodim_commutator_le_twice σ x⁻¹ y⁻¹
  simp only [inv_inv, ← z_eq_commutator, zpowers_inv] at hb
  obtain ⟨k,hk⟩ := four_dvd_fixedCodim_of_order_five σ x FiveActors.x_order
  omega

private theorem five_inverted_bound {D : Type*} [Group D]
    (σ : Representation (ZMod 2) D V) {x t : D}
    (hx : orderOf x = 5) (hinv : t * x * t⁻¹ = x⁻¹) :
    fixedCodim σ (zpowers x) ≤ 2 * fixedCodim σ (zpowers t) := by
  have hz : zpowers (x ^ 2) = zpowers x := by
    apply le_antisymm
    · exact zpowers_le.mpr ((zpowers x).pow_mem (mem_zpowers x) 2)
    · apply zpowers_le.mpr
      rw [mem_zpowers_pow_iff, hx]
      decide
  have hb := fixedCodim_commutator_le_twice σ t x
  rw [hinv, ← mul_inv_rev, ← pow_two, zpowers_inv, hz] at hb
  exact hb

private theorem hs_core_codim (σ : Representation (ZMod 2) Carrier V)
    (hf : Function.Injective σ) : 6 ≤ fixedCodim σ (zpowers coreInvolution) := by
  change 6 ≤ fixedCodim σ (zpowers EvenLocalCandidates.e0)
  have hx := hs_x_codim σ hf
  have hb := five_inverted_bound σ FiveActors.coreFive_order FiveActors.core_inverts
  have hconj : fixedCodim σ (zpowers FiveActors.coreFive) =
      fixedCodim σ (zpowers x) := by
    unfold FiveActors.coreFive
    rw [fixedCodim_zpowers_conj]
  rw [hconj] at hb
  omega

private theorem hs_product_codim (σ : Representation (ZMod 2) Carrier V)
    (hf : Function.Injective σ) : 10 ≤ fixedCodim σ (zpowers productInvolution) := by
  change 10 ≤ fixedCodim σ (zpowers Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.t)
  have hz := hs_center_codim σ hf
  have hb := five_inverted_bound σ FiveActors.productFive_order FiveActors.product_inverts
  have hconj : fixedCodim σ (zpowers FiveActors.productFive) =
      fixedCodim σ (zpowers z) := by
    unfold FiveActors.productFive
    rw [fixedCodim_zpowers_conj]
  rw [hconj] at hb
  omega

/-- Every native inner involution moves at least six dimensions in any faithful binary action. -/
theorem hs_involution_fixedCodim_ge_six (σ : Representation (ZMod 2) Carrier V)
    (hf : Function.Injective σ) {t : Carrier} (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    6 ≤ fixedCodim σ (zpowers t) := by
  have ho : orderOf t = 2 := orderOf_eq_prime ht2 ht
  rcases Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.involution_classes t ho with hc | hp
  · obtain ⟨g,hg⟩ := isConj_iff.mp hc
    rw [← hg, fixedCodim_zpowers_conj]
    exact hs_core_codim σ hf
  · obtain ⟨g,hg⟩ := isConj_iff.mp hp
    rw [← hg, fixedCodim_zpowers_conj]
    exact (by decide : 6 ≤ 10).trans (hs_product_codim σ hf)

variable {G : Type*} [Group G] [Finite G]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
/-- The HS branch of B.4.2 is excluded on the original ambient representation. -/
theorem not_ff_hs (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.hs.Carrier)) :
    ¬ IsFFModule ρ := by
  rcases h.fitting with rfl
  let hs : ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.SourceHypotheses ρ := {
    sqtk := h.sqtk, quasisimple := h.quasisimple, faithful := h.faithful,
    irreducible := h.irreducible, centralQuotient := he }
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  obtain ⟨e⟩ := he
  have hc := Theory.SpecificGroups.J2HSMultipliers.HS.center_isPGroup_of_quotient_equiv e
  obtain ⟨f,σ,hf,hi,hmark⟩ := Twenty.Inner.exists_marked_carrier_representation hs hc
  obtain ⟨a,ha,hdegree⟩ := AbsoluteWindow.finrank_eq_fixed_add_twenty_mul σ hf
  have hdim : 20 ≤ Module.finrank (ZMod 2) V := by omega
  intro hff
  obtain ⟨A,hA,_,hcodim⟩ := (cubicRatio_le_nat_iff ρ 1).mp
    (by simpa only [Nat.cast_one] using (isFFModule_iff_cubicRatio_le_one ρ).mp hff)
  have hr : rank A ≤ 5 := hA.rank_le_of_primeRank_le hs.twoRank_le_five
  have hsmall : fixedCodim ρ A ≤ rank A := by simpa only [one_mul] using hcodim
  have hmono {t : G} (ht : t ∈ A) : fixedCodim ρ (zpowers t) ≤ fixedCodim ρ A := by
    have hh := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ht))
    have h₁ := fixedCodim_add_finrank ρ (zpowers t)
    have h₂ := fixedCodim_add_finrank ρ A
    omega
  by_cases hr2 : 2 ≤ rank A
  · obtain ⟨t,htA,htL,ht,ht2⟩ := Twenty.exists_inner_involution hs hA hr2
    let tL : generalizedFitting G := ⟨t,htL⟩
    have htL1 : tL ≠ 1 := fun hh => ht (congrArg Subtype.val hh)
    have htL2 : tL ^ 2 = 1 := Subtype.ext ht2
    have hb := hs_involution_fixedCodim_ge_six σ hf
      (show f tL ≠ 1 from fun hh => htL1 (f.injective (hh.trans (map_one f).symm)))
      (show (f tL)^2 = 1 by rw [← map_pow,htL2,map_one])
    have heq : fixedSpace σ (zpowers (f tL)) = fixedSpace ρ (zpowers t) := by
      ext v
      simp only [mem_fixedSpace_zpowers_iff, hmark]
      change ρ (t : G) v = v ↔ ρ t v = v
      rfl
    have hcod : fixedCodim σ (zpowers (f tL)) = fixedCodim ρ (zpowers t) := by
      unfold fixedCodim
      rw [heq]
    rw [hcod] at hb
    have htA' := hmono htA
    omega
  · let := hA.2
    obtain ⟨t,htA,ht⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have ht2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) t htA
    obtain ⟨c,hc⟩ := hs.five_conjugates t ht ht2
    let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) := IsQuasisimple.simple
    let : Nontrivial (generalizedFitting G) :=
      (QuotientGroup.mk'_surjective (center (generalizedFitting G))).nontrivial
    have hfix : fixedSpace ρ (generalizedFitting G) = ⊥ :=
      invariants_eq_bot_of_faithful_irreducible (ρ.comp (generalizedFitting G).subtype)
        (h.faithful.comp (generalizedFitting G).subtype_injective) h.irreducible
    have hd := finrank_le_mul_fixedCodim_of_conjugates ρ (generalizedFitting G) hfix t c hc
    have htA' := hmono htA
    omega
end CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
