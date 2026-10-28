module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Triality.Complete
public import Theory.Representation.ReeF4.BinaryDegree.SchurDescent
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.Inversion
public import Theory.Representation.BinaryOffender.UniformFixedSpace
/-!
# Triality degree and outer-actor elimination on the cubic source domain

The genuine finite tensor classification, exact Frobenius character period,
and basic D4 dimensions give binary degree at least 24r. Central-cover
triviality transports this estimate to the original component. On an ambient
outer involution, the existing Schur-operator estimate moves at least 7/16
of the whole module. Its binary displacement is therefore greater than 10r,
whereas an elementary actor of ratio at most two moves at most 10r dimensions.
Thus every possible cubic actor is contained in the original component.

The inner natural and adjoint module exclusions remain to be proved. These
reductions do not assert the full triality exclusion and add no hypotheses
to the source domain. Source: Aschbacher--Smith K.3, printed p.457/PDF468;
Guralnick--Malle II, Lemma 8.6, internal pp.56--57, Theorem 8.1/Table 17.
-/

public noncomputable section
open scoped MonoidAlgebra
open Subgroup Theory.GroupTheory
open Representation Representation.FrobeniusTensor Representation.BinaryOffender
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
open Triality.RestrictedWeights Triality.RestrictedWeights.Concrete
open Triality.RestrictedWeights.SteinbergTensors
open Triality.Standard Triality.SimplyConnected
namespace CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
universe u v

theorem triality_model_degree {n : ℕ} (hn : 0 < n)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (BinaryCarrier n hn) V)
    [IsIrreducible ρ] (hf : Function.Injective ρ) :
    24 * n ≤ Module.finrank (ZMod 2) V := by
  let k := Closure ρ
  let hu := source_universal k
  let σ := absoluteRep ρ
  have hiσ : IsIrreducible (FDRep.of σ).ρ := absoluteRepIrreducible ρ
  have hfσ : Function.Injective (FDRep.of σ).ρ := absoluteRep_injective ρ hf
  obtain ⟨a, ⟨e⟩, _⟩ := native_tensor_exhaustive k hu n hn (FDRep.of σ) hiσ
  let R := tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
    (nativePointHom k n hn) (extendWeights hn a) n
  have hR : Function.Injective R.ρ := by
    intro x y hxy
    apply hfσ
    apply e.conj.injective
    simpa only [Representation.Equiv.conj_apply_self] using hxy
  have hchar (r : ℕ) :
      (∀ g, Representation.character R.ρ g ^ (2 ^ r) = Representation.character R.ρ g) ↔
        Module.finrank (ZMod 2) (SchurField ρ) ∣ r := by
    have he : Representation.character R.ρ = Representation.character σ :=
      (Representation.char_iso e).symm
    rw [he]
    exact character_pow_iff ρ r
  let s := Module.finrank (ZMod 2) (SchurField ρ)
  have hs : 0 < s := schurField_finrank_pos ρ
  have hsn : s ∣ 3 * n := (hchar _).mp
    ((native_tensor_character_period k hu n hn a _).mpr (extendWeights_period_three hn a))
  have hp : Function.Periodic (extendWeights hn a) s :=
    (native_tensor_character_period k hu n hn a _).mp ((hchar _).mpr (dvd_refl s))
  obtain ⟨i, hi⟩ := native_tensor_nonzero_weight k hu n hn (extendWeights hn a)
    (EvenInvolutionGeometry.longRoot n hn 1)
    (EvenInvolutionGeometry.longRoot_orderOf n hn one_ne_zero) hR
  have hprod := Triality.BinaryDegree.twenty_four_mul_le_twisted_product hn hs hsn
    (extendWeights_wrap hn a) Triality.InnerDisplacement.minimumDegree_diagram hp
    (fun j => Triality.InnerDisplacement.minimumDegree_pos (extendWeights hn a j))
    ⟨i, Triality.InnerDisplacement.minimumDegree_nonzero _ hi⟩
    (fun j => Triality.InnerDisplacement.minimumDegree_fixed (extendWeights hn a j))
  have hdim : (∏ j ∈ Finset.range n,
      Triality.InnerDisplacement.minimumDegree (extendWeights hn a j)) ≤ Module.finrank k R := by
    rw [show Module.finrank k R = ∏ j ∈ Finset.range n,
        Module.finrank k ((basicFamily k hu).factor (extendWeights hn a j)).Space from
      finrank_tensor _ _ _ _ _]
    exact Finset.prod_le_prod' (fun j _ => minimumDegree_le_basic_finrank k hu _)
  rw [binary_finrank_eq ρ]
  change 24 * n ≤ s * Module.finrank k (FDRep.of σ)
  rw [e.toLinearEquiv.finrank_eq]
  exact hprod.trans (Nat.mul_le_mul_left s hdim)

variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem triality_source_degree (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : 0 < n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (L ⧸ Subgroup.center L)) :
    24 * n ≤ Module.finrank (ZMod 2) V := by
  let := h.quasisimple
  let := h.irreducible
  have hz := Triality.InnerDisplacement.center_eq_bot_of_twoGroup (ρ.comp L.subtype)
    (h.faithful.comp Subtype.val_injective)
    (Triality.InnerDisplacement.PrimeToTwoCovers.center_isTwoGroup n hn hm)
  obtain ⟨e₀⟩ := (isTrialityGroupAt_binary_iff _ n hn).mp hm
  let e : L ≃* BinaryCarrier n hn :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans e₀
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ := (irreducible_comp_surjective_iff _ e.symm.surjective _).mpr h.irreducible
  exact triality_model_degree hn σ (h.faithful.comp (Subtype.val_injective.comp e.symm.injective))

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem ambient_irreducible (h : ChapterK.RankOne.SourceHypotheses ρ L) :
    IsIrreducible ρ := by
  let := h.irreducible
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp L.subtype)
  refine ⟨fun S => ?_⟩
  let S' : Subrepresentation (ρ.comp L.subtype) :=
    ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule g hv⟩
  rcases eq_bot_or_eq_top S' with hb | ht
  · exact Or.inl (Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation (ρ.comp L.subtype) => U.toSubmodule) hb))
  · exact Or.inr (Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation (ρ.comp L.subtype) => U.toSubmodule) ht))

omit [FiniteDimensional (ZMod 2) V] in
theorem triality_source_actor_rank (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : 0 < n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (L ⧸ center L))
    (A : Subgroup G) (hA : IsElementaryTwo A) : rank A ≤ 5 * n := by
  let := h.irreducible
  let := h.layer_normal
  let := h.quasisimple
  have hG := CharacteristicTwoIrreducible.primeRank_le_automorphisms ρ L h.faithful
  have hL := automorphism_primeRank_le_quotient_center (E := L) 2
  have hQ := Triality.Standard.TwoRank.automorphism_twoRank_eq_five_mul_of_model n hn hm
  have hb : primeRank 2 G ≤ 5 * n := hG.trans (hL.trans hQ.le)
  have hc := (primeRank_le_iff_elementary_card_le G).mp hb A hA.2
  simpa only [rank, Nat.log_pow Nat.one_lt_two] using Nat.log_mono_right (b := 2) hc

theorem triality_outer_displacement (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : 0 < n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (L ⧸ center L))
    (t : G) (ht : t ∉ L) (ht2 : t ^ 2 = 1) :
    10 * n < fixedCodim ρ (zpowers t) := by
  let := h.quasisimple
  let := h.layer_normal
  let := h.irreducible
  let : IsIrreducible ρ := ambient_irreducible h
  let K := SchurField ρ
  let : Finite ρ.asModule := Module.finite_of_finite (ZMod 2)
  let : FiniteDimensional K ρ.asModule := Module.Finite.of_finite
  let : IsIrreducible (ρ.endFieldRep.comp L.subtype) := EndField.restriction_irreducible ρ L
  have hratio : 7 * Module.finrank K ρ.asModule ≤
      16 * Module.finrank K (LinearMap.range (ρ.endFieldRep t - LinearMap.id)) := by
    by_cases hc : Representation.CentralizesCommutant ρ.endFieldRep L t
    · exact ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality.source_ratio_of_centralizesCommutant
        L n hn hm ρ.endFieldRep (EndField.injective ρ h.faithful) t ht ht2 hc
    · have hh := Representation.finrank_le_twice_displacement_of_not_centralizesCommutant
        ρ.endFieldRep L t hc
      change Module.finrank K ρ.asModule ≤
        2 * Module.finrank K (LinearMap.range (ρ.endFieldRep t - LinearMap.id)) at hh
      omega
  have hr := Nat.mul_le_mul_left (Module.finrank (ZMod 2) K) hratio
  have hdim := finrank_eq_endField_mul ρ
  have hcodim := EndField.fixedCodim_eq ρ (zpowers t)
  rw [ReeF4.FixedSpaceEstimate.BasicInvolutions.cyclic_fixedCodim_eq_rank] at hcodim
  change Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) K *
    Module.finrank K ρ.asModule at hdim
  change fixedCodim ρ (zpowers t) = Module.finrank (ZMod 2) K *
    Module.finrank K (LinearMap.range (ρ.endFieldRep t - LinearMap.id)) at hcodim
  have hd := triality_source_degree h hn hm
  nlinarith

theorem triality_small_actor_le_layer (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : 0 < n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (L ⧸ center L))
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) : A ≤ L := by
  let : IsElementaryAbelian 2 A := hA.2
  have hr := triality_source_actor_rank h hn hm A hA
  intro t ht
  by_contra hnot
  have hhigh := triality_outer_displacement h hn hm t hnot
    (elemPow_eq_one_of_isElementaryAbelian t ht)
  have hmono := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ht))
  have hdt := fixedCodim_add_finrank ρ (zpowers t)
  have hdA := fixedCodim_add_finrank ρ A
  omega

theorem triality_source_inner_actor (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : 0 < n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (L ⧸ center L)) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ IsCubic ρ A ∧ A ≤ L ∧
      rank A ≤ 5 * n ∧ fixedCodim ρ A ≤ 2 * rank A := by
  obtain ⟨A, hA, hc, hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.smallCubic
  exact ⟨A, hA, hc, triality_small_actor_le_layer h hn hm A hA hd,
    triality_source_actor_rank h hn hm A hA, hd⟩
end CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
