module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourConstrained
public import Theory.GroupTheory.PerfectSimpleOrderNormalizer

/-!
# Excluding the constrained A₈ star in the original degree-four branch

The original normalized residual has simple quotient A₈. If the escaping
constrained component has the same star group, its core-central quotient
is literally A₈ too. The residual action is nontrivial and perfect. Its inner
lift fills that simple group by order divisibility, but normalizes the
nontrivial two-group induced by the original radical. The automorphism
p-core calculation excludes this configuration, retaining possible outer
radical actors.

The final theorem applies the exclusion to the actual C.2.8 witness with its
whole doubled orbit and original radical. Only the SL₅(2) star remains here.
Source: Aschbacher--Smith C.4.3--6, 4.2.13, 4.4.6 and 12.1.9,
printed pp.152,612,620,793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter12.Section01.DoubleNaturalSource
open Chapter4.Section04.NormalizedRankOneOddControl
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- Equality of the original and constrained simple quotients forces the
full inner action, contrary to the nontrivial original radical action. -/
theorem doubledFour_no_constrained_alternating_eight
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (eF : (F ⧸ pCore 2 F) ≃* alternatingGroup (Fin 8))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* alternatingGroup (Fin 8)) : False := by
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K)))
  let eQ : Q ≃* alternatingGroup (Fin 8) :=
    ((h.constrained_star_central_equiv K hK hq hout hfK).trans
      (QuotientGroup.congr _ _ e (FixedElementary.map_center e))).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
        QuotientGroup.quotientBot)
  let q := (eF.trans eQ.symm).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hqsur : Function.Surjective q :=
    (eF.trans eQ.symm).surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 F :=
    (MonoidHom.ker_comp_of_injective _ _ (eF.trans eQ.symm).injective).trans
      (QuotientGroup.ker_mk' _)
  let : Group.IsNilpotent (pCore 2 F) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := hqker.symm ▸ inferInstance
  have hspan := h.normalized_span_eq hn
  let : Group.IsPerfect F := hspan ▸ h.span_perfect
  let A := F.subgroupOf H
  let B := coreCentralActorImage K A
  let U := coreCentralActorImage K (R.subgroupOf H)
  have hFH : F ≤ H := h.component_le.trans h.local_le
  have hAK : A ≤ normalizer (K : Set H) := by
    simpa only [hspan] using h.constrained_span_normalizes_intrinsic K hK hq
  let aF : F ≃* A.subgroupOf (normalizer (K : Set H)) :=
    (subgroupOfEquivOfLe hFH).symm.trans (subgroupOfEquivOfLe hAK).symm
  let b : F →* B := ((normalizerCoreCentralAction K).subgroupMap
    (A.subgroupOf (normalizer (K : Set H)))).comp aF.toMonoidHom
  have hb : Function.Surjective b :=
    ((normalizerCoreCentralAction K).subgroupMap_surjective _).comp aF.surjective
  let a := B.subtype.comp b
  have har : a.range = B := by rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hb,←MonoidHom.range_eq_map,range_subtype]
  have hane : a ≠ 1 := by
    intro he
    apply h.constrained_span_action_nontrivial K hK hq hout
    rw [hspan]
    change B = ⊥
    rw [←har,he,MonoidHom.range_one]
  have hAR : A ≤ normalizer (R.subgroupOf H : Set H) := by
    intro a ha r
    exact h.span_normalizes_radical (hspan.symm ▸ ha) (r : G)
  have hU : IsPGroup 2 U := h.isRadical.isPGroup.comap_subtype.map _
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp ht)).elim
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  apply h.constrained_radical_action_nontrivial K hK hq hout hfK
  exact MulAut.perfect_simple_quotient_normalizer_p_eq_bot hz q hqsur a hane U hU
    (har ▸ coreCentralActorImage_normalizes K A (R.subgroupOf H) hAR)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter12.Section01.DoubleNaturalSource
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter1.RadicalExclusions.ModelReduction
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
include D h

/-- The only surviving constrained star group is the actual SL₅(2). -/
theorem doubledFour_pushingUp_linear_five_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H U : Subgroup G, Witness L V A J H U ∧
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        generalizedFitting K = pCore 2 K ∧
        Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2)) := by
  obtain ⟨J,H,U,hw,hWU,hWJ,K,hK,hq,hout,hcon,hmodels⟩ :=
    D.doubledFour_pushingUp_two_linear_models_of_many h hmany B A hA ho hnot
  refine ⟨J,H,U,hw,hWU,hWJ,K,hK,hq,hout,hcon,?_⟩
  rcases hmodels with he | he
  · obtain ⟨eK⟩ := he
    have hc := hw.2.2.2.2.2.2.1
    have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hw.2.2.2.2.2.2.2.2.1
    obtain ⟨e,_⟩ := hw.2.2.2.2.2.2.2.2.2.2.2.1
    exact (doubledFour_no_constrained_alternating_eight hc hn
      (e.trans (B.component.trans doubledFour_linearEquiv)) K hK hq hout hcon eK).elim
  · exact he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
