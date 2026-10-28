module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.ReeF4.ElementaryTwoBound
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.FiniteSource
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.Source
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.CompleteSource
public import Theory.Representation.Triality.InnerDisplacement.CoverReduction
public import Theory.Representation.BinaryOffender.CubicFixedSpaceSaturation
public import Theory.Representation.BinaryOffender.InvolutionFixedKernel
/-!
# The saturated Ree F4 actor on the original cubic source domain

The completed finite tensor classification and covering calculation give
fixed codimension at least 10(2m+1) for every original involution. The
elementary rank bound is 5(2m+1). A ratio-at-most-two actor therefore attains
both bounds, and its fixed space equals that of each nonidentity element.
It is quadratic and equals the pointwise kernel on any such fixed space
inside the literal involution centralizer. In particular normality is relative
to that centralizer, not normality in the ambient group.

This proves the equality reduction, including arbitrary source covers and
outer actors. The local centralizer contradiction remains to be proved;
no Ree exclusion is claimed here. Source: Aschbacher--Smith K.3, printed
p.457/PDF468; Guralnick--Malle II, Lemmas 2.3 and 8.8, internal pp.6 and57,
and Theorem8.1/Table17.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.AlgebraicGroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
universe u v
variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem ree_model_involution_bound {m : ℕ} (hm : 1 ≤ m) :
    ReeF4.FixedSpaceEstimate.BinaryModelInvolutionBound.{v} m := by
  apply ReeF4.FixedSpaceEstimate.binaryModelInvolutionBound_of_class_bound_and_semisimple_centers
  · intro F _ _ _ H _ hH T hT
    exact SemisimpleCenterContainment.center_le_maximalTorus_of_semisimple hH hT
  · exact ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.model_odd_class_bound m
  · exact hm

theorem ree_source_involution_bound (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e₀ : L ⧸ center L ≃* ReeF4.Model m)
    (t : G) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    10 * (2 * m + 1) ≤ fixedCodim ρ (zpowers t) := by
  let := h.quasisimple
  let := h.irreducible
  let := h.layer_normal
  have hz := Triality.InnerDisplacement.center_eq_bot_of_twoGroup (ρ.comp L.subtype)
    (h.faithful.comp Subtype.val_injective)
    (ReeF4.CentralCovers.OddPrimary.center_isPGroup_of_quotient_equiv m hm e₀)
  let e : L ≃* ReeF4.Model m :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans e₀
  have htL : t ∈ L := by
    let : IsElementaryAbelian 2 (zpowers t) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one ht2
    exact (ReeF4.elementary_le_of_generalizedFitting L hm h.fitting e₀ (zpowers t)) (mem_zpowers t)
  let tL : L := ⟨t, htL⟩
  have hb := ReeF4.FixedSpaceEstimate.binary_bound_of_equiv (ree_model_involution_bound hm)
    e (ρ.comp L.subtype) h.irreducible (h.faithful.comp Subtype.val_injective)
    tL (fun he => ht (congrArg Subtype.val he)) (Subtype.ext ht2)
  have heq : invariants ((ρ.comp L.subtype).comp (zpowers tL).subtype) =
      invariants (ρ.comp (zpowers t).subtype) :=
    ReeF4.FixedSpaceEstimate.invariants_comp_zpowers ρ L.subtype tL
  rw [heq] at hb
  exact hb

theorem ree_source_actor_rank (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e : L ⧸ center L ≃* ReeF4.Model m)
    (A : Subgroup G) (hA : IsElementaryTwo A) : rank A ≤ 5 * (2 * m + 1) := by
  let := h.quasisimple
  let := h.irreducible
  let := h.layer_normal
  let : IsElementaryAbelian 2 A := hA.2
  have hAL := ReeF4.elementary_le_of_generalizedFitting L hm h.fitting e A
  let B := A.subgroupOf L
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAL
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hcard : Nat.card (B.map π) = Nat.card B := by
    change Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (center L)))) = _
    rw [← Subgroup.map_map, Subgroup.card_map_of_injective e.injective]
    exact card_map_centralQuotient (p := 2) (ρ.comp L.subtype)
      (h.faithful.comp Subtype.val_injective) B
  have hb := ReeF4.ElementaryTwoBound.card_le m hm (B.map π) (IsElementaryAbelian.map π)
  rw [hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv] at hb
  simpa only [rank, Nat.log_pow Nat.one_lt_two] using Nat.log_mono_right (b := 2) hb

theorem ree_small_actor_saturated (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e : L ⧸ center L ≃* ReeF4.Model m)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    A ≤ L ∧ rank A = 5 * (2 * m + 1) ∧ fixedCodim ρ A = 10 * (2 * m + 1) ∧
      IsQuadratic ρ A ∧ ∀ t ∈ A, t ≠ 1 →
        fixedCodim ρ (zpowers t) = 10 * (2 * m + 1) ∧
        fixedSpace ρ A = fixedSpace ρ (zpowers t) := by
  let := h.quasisimple
  let := h.layer_normal
  let : IsElementaryAbelian 2 A := hA.2
  have hr := ree_source_actor_rank h hm e A hA
  have he (t : G) (ht : t ∈ A) (ht1 : t ≠ 1) :
      fixedCodim ρ A = 10 * (2 * m + 1) ∧
      fixedCodim ρ (zpowers t) = 10 * (2 * m + 1) ∧
      fixedSpace ρ A = fixedSpace ρ (zpowers t) := by
    have hb := ree_source_involution_bound h hm e t ht1
      (elemPow_eq_one_of_isElementaryAbelian t ht)
    have hmono := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ht))
    have hdA := fixedCodim_add_finrank ρ A
    have hdt := fixedCodim_add_finrank ρ (zpowers t)
    have hdim : fixedCodim ρ A = fixedCodim ρ (zpowers t) := by omega
    exact ⟨by omega, by omega, fixedSpace_eq_of_fixedCodim_eq ρ (zpowers_le.mpr ht) hdim⟩
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hsat := he t ht ht1
  refine ⟨ReeF4.elementary_le_of_generalizedFitting L hm h.fitting e A,
    by omega, hsat.1, ?_, fun t ht ht1 => (he t ht ht1).2⟩
  exact isQuadratic_of_common_fixedSpace ρ (fun t ht ht1 => (he t ht ht1).2.2)

theorem ree_source_saturated_actor (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e : L ⧸ center L ≃* ReeF4.Model m) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ A ≤ L ∧ rank A = 5 * (2 * m + 1) ∧
      fixedCodim ρ A = 10 * (2 * m + 1) ∧ IsQuadratic ρ A ∧
      ∀ t ∈ A, t ≠ 1 → fixedCodim ρ (zpowers t) = 10 * (2 * m + 1) ∧
        fixedSpace ρ A = fixedSpace ρ (zpowers t) := by
  obtain ⟨A, hA, _, hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.smallCubic
  exact ⟨A, hA, ree_small_actor_saturated h hm e A hA hsmall⟩

theorem ree_saturated_actor_eq_fixedKernel (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e : L ⧸ center L ≃* ReeF4.Model m)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A)
    (t : G) (ht : t ∈ A) (ht1 : t ≠ 1) :
    A = involutionFixedKernel ρ t := by
  let : IsElementaryAbelian 2 A := hA.2
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have hsat := ree_small_actor_saturated h hm e A hA hsmall
  have hfix := (hsat.2.2.2.2 t ht ht1).2
  have hAK : A ≤ involutionFixedKernel ρ t := by
    intro a ha
    refine ⟨mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨t, ht⟩)
    · intro v hv
      exact (hfix.symm ▸ hv) ⟨a, ha⟩
  have hK : IsElementaryTwo (involutionFixedKernel ρ t) :=
    ⟨fun he => hA.1 (bot_unique (he ▸ hAK)),
      involutionFixedKernel_elementary ρ h.faithful t ht2⟩
  have hr := ree_source_actor_rank h hm e _ hK
  apply Subgroup.eq_of_le_of_card_ge hAK
  rw [hK.card_eq_two_pow_rank, hA.card_eq_two_pow_rank, hsat.2.1]
  exact Nat.pow_le_pow_right (by decide) hr

theorem ree_source_normal_actor (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e : L ⧸ center L ≃* ReeF4.Model m) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ A ≤ L ∧ rank A = 5 * (2 * m + 1) ∧
      fixedCodim ρ A = 10 * (2 * m + 1) ∧ IsQuadratic ρ A ∧
      ∀ t ∈ A, t ≠ 1 → A = involutionFixedKernel ρ t ∧
        (A.subgroupOf (centralizer {t})).Normal ∧
        fixedSpace ρ A = fixedSpace ρ (zpowers t) := by
  obtain ⟨A, hA, hc, hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.smallCubic
  have hsat := ree_small_actor_saturated h hm e A hA hd
  refine ⟨A, hA, hsat.1, hsat.2.1, hsat.2.2.1, hsat.2.2.2.1, ?_⟩
  intro t ht ht1
  have he := ree_saturated_actor_eq_fixedKernel h hm e A hA hd t ht ht1
  exact ⟨he, he.symm ▸ involutionFixedKernel_normal ρ t, (hsat.2.2.2.2 t ht ht1).2⟩
end CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
