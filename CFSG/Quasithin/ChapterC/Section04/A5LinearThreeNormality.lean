module
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedOddNormality
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.A5ActionRank
public import Theory.GroupTheory.PerfectAutomorphismStabilizer
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SL3Local
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison

/-!
# The constrained linear-three normalizer obstruction

The genuine C.2.7 star map identifies the component central quotient with
PSL₃ over its marked binary field. For fields of order at least four, the
source large-order placement makes the radical intersection nontrivial.
Its image remains nontrivial after dividing by the scalar center of order
one or three, because it is a two-group.

The original perfect conjugate span stabilizes that literal image. Soluble
outer automorphisms realize this action faithfully inside PSL₃, where the
two-local parabolic theorem bounds its five-rank by one. Odd-rank component
normality and the original A₅ pair action then imply local normality.

Source: Aschbacher–Smith C.2.7, C.4.5–8, printed pp.145–147,152–154,
with the original A₅ covering data of 4.2.12–13, pp.610–611.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.Section04Constrained
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {H M K R : Subgroup G}

noncomputable def source_linear_three_equiv
    (h : Input KnownSimple.IsKnownSimple H R M K)
    {F : Type*} [Field F] [Finite F]
    (e : starImage K R K ≃* SL(3,F)) : coreCentralQuotient K ≃* PSL(3,F) := by
  let := h.quasisimple
  let c : PerfectCentralCovering.Cover (K ⧸ pCore 2 K) (starImage K R K) :=
    { toMonoidHom := coreToStar h.normalizes
      surjective := coreToStar_surjective h.normalizes
      isPerfect := inferInstance
      ker_le_center := C27Source.coreToStar_ker_central_from_source h }
  exact c.quotientCenterEquiv.trans
    (QuotientGroup.congr _ _ e (FixedElementary.map_center e))

theorem source_linear_three_equiv_apply
    (h : Input KnownSimple.IsKnownSimple H R M K)
    {F : Type*} [Field F] [Finite F]
    (e : starImage K R K ≃* SL(3,F)) (k : K) :
    source_linear_three_equiv h e (coreCentralProjection K k) =
      Matrix.PSL3.projection F (e (toStarImage K R k)) := by rfl

theorem linear_three_large_card {F : Type*} [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) : 40320 < Nat.card SL(3,F) := by
  have hc := (center SL(3,F)).index_mul_card
  rw [Atlas.ExceptionalSupport.card_sl_center] at hc
  change Nat.card PSL(3,F) * Nat.gcd 3 (Nat.card F - 1) = Nat.card SL(3,F) at hc
  rw [← hc,Matrix.PSL3.LinearThree.card_projective_mul_scalar]
  have hb := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.pow_le_pow_left hF 3)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hF 3) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hF 2) 1)
  exact lt_of_lt_of_le (by norm_num : 40320 < 4^3*(4^3-1)*(4^2-1)) hb

theorem source_linear_three_intersection_ne_bot
    (h : Input KnownSimple.IsKnownSimple H R M K)
    {F : Type*} [Field F] [Finite F]
    (e : starImage K R K ≃* SL(3,F)) (hF : 4 ≤ Nat.card F) :
    coreCentralIntersectionImage K R ≠ ⊥ := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  have hlarge : 40320 < Nat.card (starImage K R K) := by
    rw [Nat.card_congr e.toEquiv]
    exact linear_three_large_card hF
  have hn := (C27Source.star_intersection_placement_from_source_of_large_order h hlarge).1.1
  have he := C27Source.component_intersection_star_eq_of_normal_input (C27Source.source_join_input h)
  rw [← he] at hn
  let P := ((R.subgroupOf K).map (toStarImage K R)).map e.toMonoidHom
  have hr : IsPGroup 2 R := by
    exact h.setup.radical.isPGroup.of_equiv (subgroupOfEquivOfLe h.setup.radical_le)
  have hp : IsPGroup 2 P := (hr.comap_subtype.map _).map _
  have hpc : Disjoint P (center SL(3,F)) := hp.disjoint_of_coprime
    (IsPGroup.of_card_dvd_pow (n := 1) (by simpa using Matrix.SL3.card_center_dvd_three F))
    (by decide : Nat.Coprime 2 3)
  intro hb
  have hm : (coreCentralIntersectionImage K R).map (source_linear_three_equiv h e).toMonoidHom =
      P.map (Matrix.PSL3.projection F) := by
    rw [coreCentralIntersectionImage, map_map, map_map, map_map]
    congr 1
  rw [hb,Subgroup.map_bot] at hm
  have hpbot : P = ⊥ := by
    have hpz : P ≤ center SL(3,F) := by
      simpa only [Matrix.PSL3.projection_ker] using (map_eq_bot_iff P).mp hm.symm
    exact le_bot_iff.mp ((le_inf le_rfl hpz).trans hpc.eq_bot.le)
  exact hn ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hpbot)
end CFSG.Quasithin.ChapterC.Section04Constrained

namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

theorem constrained_linear_three_intersection_or_span_rank
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : coreCentralQuotient K ≃* PSL(3,F)) :
    coreCentralIntersectionImage K (R.subgroupOf H) = ⊥ ∨
      primeRank 5 (coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H)) ≤ 1 := by
  let Q := coreCentralQuotient K
  let A := (conjugateSpanBy L M).subgroupOf H
  let B := coreCentralActorImage K A
  let U := coreCentralIntersectionImage K (R.subgroupOf H)
  by_cases hu : U = ⊥
  · exact Or.inl hu
  right
  let := hq
  let X := conjugateSpanBy L M
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  let : Group.IsPerfect B := coreCentralActorImage_perfect K A
    (h.constrained_span_normalizes_intrinsic K hK hq)
  have hAR : A ≤ normalizer (R.subgroupOf H : Set H) := by
    intro a ha y
    exact h.span_normalizes_radical ha (y : G)
  have hU : IsPGroup 2 U := coreCentralIntersectionImage_isPGroup K _ h.isRadical.isPGroup
  let D := PSL(3,F)
  let P := U.map e.toMonoidHom
  let B' := B.map (MulAut.congr e).toMonoidHom
  have hP : P ≠ ⊥ := fun hp => hu ((U.map_eq_bot_iff_of_injective e.injective).mp hp)
  let : Group.IsPerfect B' := Group.IsPerfect.map _
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  let : Group.IsSolvable (MulAut.Outer D) := MulAut.isSolvable_outer_of_mulEquiv e.symm
  let : IsSimpleGroup Q := hq.simple
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hc)).elim
  have hzD : center D = ⊥ := by
    rw [← FixedElementary.map_center e,hz,Subgroup.map_bot]
  obtain ⟨f,hf,hconj⟩ := MulAut.perfect_subgroup_exists_inner_lift B' hzD
  have hb : primeRank 5 B' ≤ 1 := by
    by_contra! hb
    apply OrdinaryPlacement.SL3Local.no_perfect_five_rank_two_in_two_normalizer
      P (hU.map e.toMonoidHom) hP (by omega) f hf
    rintro _ ⟨a,rfl⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hconj a]
    exact coreCentralActorImage_map_stabilizes K A (R.subgroupOf H) hAR e a.property
  exact (primeRank_equiv 5 (B.equivMapOfInjective (MulAut.congr e).toMonoidHom
    (MulAut.congr e).injective)).le.trans hb
end CFSG.Quasithin.ChapterC.HypothesisC28

namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource Section04Constrained
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

@[expose] noncomputable def constrained_linear_three_simple_equiv
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(3,F)) :
    coreCentralQuotient K ≃* PSL(3,F) :=
  (coreCentralQuotientCongr (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
    (source_linear_three_equiv (h.constrained_source_input K hK hq hout hfK) e)

theorem constrained_linear_three_span_fiveRank_le_one
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(3,F))
    (hF : 4 ≤ Nat.card F) :
    primeRank 5 (coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H)) ≤ 1 := by
  let eK := K.equivMapOfInjective H.subtype H.subtype_injective
  let ec := coreCentralQuotientCongr eK
  have he : (coreCentralIntersectionImage K (R.subgroupOf H)).map ec.toMonoidHom =
      coreCentralIntersectionImage (K.map H.subtype) R := by
    ext x
    constructor
    · rintro ⟨y,⟨k,hk,rfl⟩,rfl⟩
      exact ⟨eK k,hk,(coreCentralQuotientCongr_apply eK k).symm⟩
    · rintro ⟨k,hk,rfl⟩
      refine ⟨coreCentralProjection K (eK.symm k),⟨eK.symm k,?_,rfl⟩,?_⟩
      · change ((eK.symm k : K) : H).val ∈ R
        have hh := congrArg (fun a : K.map H.subtype => (a : G)) (eK.apply_symm_apply k)
        change ((eK.symm k : K) : H).val = (k : G) at hh
        rwa [hh]
      · change coreCentralQuotientCongr eK (coreCentralProjection K (eK.symm k)) = _
        rw [coreCentralQuotientCongr_apply,eK.apply_symm_apply]
  have hne : coreCentralIntersectionImage K (R.subgroupOf H) ≠ ⊥ := by
    intro hb
    apply source_linear_three_intersection_ne_bot
      (h.constrained_source_input K hK hq hout hfK) e hF
    rw [←he,hb,Subgroup.map_bot]
  exact (h.constrained_linear_three_intersection_or_span_rank K hK hq
    (h.constrained_linear_three_simple_equiv K hK hq hout hfK e)).resolve_left hne

theorem normalizes_a5_of_constrained_star_linear_three_large
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(3,F.Carrier)) :
    M ≤ normalizer (L : Set G) := by
  let : K.Normal := h.constrained_linear_three_component_normal K hK hq hout hfK F hF e
  apply h.normalizes_of_a5_component_action_fiveRank_le_one a K
    (h.constrained_span_action_nontrivial K hK hq hout)
  apply h.constrained_linear_three_span_fiveRank_le_one K hK hq hout hfK e
  rw [F.card_eq]
  exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
end CFSG.Quasithin.ChapterC.HypothesisC28
