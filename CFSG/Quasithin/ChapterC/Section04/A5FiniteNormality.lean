module
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedCubicNormality
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.A5ActionRank
public import Theory.GroupTheory.PerfectAutomorphismStabilizer
public import Theory.Alternating.PrimeRank
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.SpecificGroups.Classical.BinaryFiveRanks
public import Theory.SpecificGroups.FFG2DerivedCenter
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# Finite constrained rows in the original A₅ configuration

The source bounds the selected component's core center by three. Cubic
rank at least two therefore makes it normal in H. Its perfect span action
is inner on the simple central quotient, so five-rank at most one there
contradicts the original nonnormal A₅ pair action.

The literal star maps discharge both bounds for A₆, A₇, A₈, the triple
cover of A₆, G₂(2)′, and SL₅(2). All subgroups, radical and quotient maps remain
those of C.2.8; original normality is a conclusion.

Source: Aschbacher–Smith C.2.7(3), C.4.5–8, printed pp.145–147,152–154,
specialized to the A₅ covering configuration of 4.2.12–13, pp.610–611.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

theorem constrained_span_action_rank_le_central_quotient
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p : ℕ) :
    primeRank p (coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H)) ≤
      primeRank p (coreCentralQuotient K) := by
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let X := conjugateSpanBy L M
  let A := X.subgroupOf H
  let B := coreCentralActorImage K A
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  let : Group.IsPerfect B := coreCentralActorImage_perfect K A
    (h.constrained_span_normalizes_intrinsic K hK hq)
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hc)).elim
  obtain ⟨f,hf,_⟩ := MulAut.perfect_subgroup_exists_inner_lift B hz
  exact Theory.GroupTheory.primeRank_le_of_injective p f hf

theorem normalizes_a5_of_constrained_central_ranks
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (hr3 : 2 ≤ primeRank 3 (coreCentralQuotient K))
    (hr5 : primeRank 5 (coreCentralQuotient K) ≤ 1) :
    M ≤ normalizer (L : Set G) := by
  let : K.Normal := h.constrained_component_normal_of_central_threeRank K hK hq hout hfK hr3
  exact h.normalizes_of_a5_component_action_fiveRank_le_one a K
    (h.constrained_span_action_nontrivial K hK hq hout)
    ((h.constrained_span_action_rank_le_central_quotient K hK hq 5).trans hr5)

theorem normalizes_a5_of_constrained_central_alternating
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {n : ℕ} (hn : 6 ≤ n) (hn8 : n ≤ 8)
    (e : coreCentralQuotient K ≃* alternatingGroup (Fin n)) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_a5_of_constrained_central_ranks a K hK hq hout hfK
  · rw [primeRank_congr 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank hn
  · rw [primeRank_congr 5 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime n 5 (by decide) (by decide)]
    omega

theorem normalizes_a5_of_constrained_star_alternating
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {n : ℕ} (hn : 6 ≤ n) (hn8 : n ≤ 8)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* alternatingGroup (Fin n)) :
    M ≤ normalizer (L : Set G) := by
  let ec := (coreCentralQuotientCongr
    (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
      (Section04Constrained.source_simple_equiv
        (h.constrained_source_input K hK hq hout hfK) e
        (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega))))
  exact h.normalizes_a5_of_constrained_central_alternating a K hK hq hout hfK hn hn8 ec

theorem normalizes_a5_of_constrained_star_triple_six
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (e : (starImage (K.map H.subtype) R (K.map H.subtype) ⧸
      center (starImage (K.map H.subtype) R (K.map H.subtype))) ≃*
      alternatingGroup (Fin 6)) : M ≤ normalizer (L : Set G) := by
  exact h.normalizes_a5_of_constrained_central_alternating a K hK hq hout hfK
    (by decide) (by decide) ((h.constrained_star_central_equiv K hK hq hout hfK).trans e)

theorem normalizes_a5_of_constrained_star_linear_five_two
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : M ≤ normalizer (L : Set G) := by
  let ec := (h.constrained_star_central_equiv K hK hq hout hfK).trans
    (QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e))
  apply h.normalizes_a5_of_constrained_central_ranks a K hK hq hout hfK
  · rw [primeRank_congr 3 ec]
    exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two
  · rw [primeRank_congr 5 ec]
    exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_fiveRank_le_one

theorem normalizes_a5_of_constrained_star_g2_derived_two
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) : M ≤ normalizer (L : Set G) := by
  let ec := (coreCentralQuotientCongr
    (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
      (Section04Constrained.source_simple_equiv
        (h.constrained_source_input K hK hq hout hfK) e
        Theory.SpecificGroups.g2_derived_two_center_eq_bot)
  apply h.normalizes_a5_of_constrained_central_ranks a K hK hq hout hfK
  · rw [primeRank_congr 3 ec]
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2
  · rw [primeRank_congr 5 ec]
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    apply primeRank_le_one_of_square_not_dvd
    rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
    decide

end CFSG.Quasithin.ChapterC.HypothesisC28
