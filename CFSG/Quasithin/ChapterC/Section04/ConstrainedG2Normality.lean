module
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedCubicNormality
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.A5ActionRank
public import Theory.AtlasPort.LinearGroups.G2.PerfectAutomorphismNormalizer
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank

/-!
# The actual constrained G₂ row of original A₅ normality

The full C.2.7 moved-section theorem places the original radical intersection
inside the large G₂ star component and makes it nontrivial. The perfect
conjugate span stabilizes that literal image, so its action has odd-prime
rank at most one. Cubic rank two and the source core-center bound make the
selected C-component normal. The original nonnormal A₅ pair would retain
five-rank at least two in this nontrivial action, giving a contradiction.

Every action and quotient map is the one supplied by the genuine C.2.8
configuration. The final row consumes the literal binary-field star marking
and leaves no normality, intersection, or local-geometry premise.

Source: Aschbacher–Smith C.2.7(3), C.4.5–8, printed pp.146–147,152–154.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

theorem constrained_g2_intersection_or_span_rank
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : coreCentralQuotient K ≃* Atlas.G2.Model F) (hF : 4 ≤ Nat.card F)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    coreCentralIntersectionImage K (R.subgroupOf H) = ⊥ ∨
      primeRank p (coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H)) ≤ 1 := by
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
  let D := Atlas.G2.Model F
  let P := U.map e.toMonoidHom
  let B' := B.map (MulAut.congr e).toMonoidHom
  have hP : P ≠ ⊥ := fun hp => hu ((U.map_eq_bot_iff_of_injective e.injective).mp hp)
  let : Group.IsPerfect B' := Group.IsPerfect.map _
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  let : Group.IsSolvable (MulAut.Outer D) :=
    MulAut.isSolvable_outer_of_mulEquiv e.symm
  have hb := Atlas.G2.PerfectSubgroups.perfect_automorphism_stabilizer_odd_rank_le_one
    P (hU.map e.toMonoidHom) hP (by omega) B'
    (coreCentralActorImage_map_stabilizes K A (R.subgroupOf H) hAR e) ho
  exact (primeRank_equiv p (B.equivMapOfInjective (MulAut.congr e).toMonoidHom
    (MulAut.congr e).injective)).le.trans hb
end CFSG.Quasithin.ChapterC.HypothesisC28

namespace CFSG.Quasithin.ChapterC.Section04Constrained
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

variable {G : Type*} [Group G] [Finite G] {H M K R : Subgroup G}

variable {F : Type*} [Field F] [Finite F]

private theorem g2_card_large (hF : 4 ≤ Nat.card F) : 40320 < Nat.card (Atlas.G2.Model F) := by
  rw [Atlas.G2.card_Model]
  have h6 := Nat.pow_le_pow_left hF 6
  have h2 := Nat.pow_le_pow_left hF 2
  have hh := Nat.mul_le_mul (Nat.mul_le_mul h6 (Nat.sub_le_sub_right h6 1))
    (Nat.sub_le_sub_right h2 1)
  exact lt_of_lt_of_le (by norm_num : 40320 < 4 ^ 6 * (4 ^ 6 - 1) * (4 ^ 2 - 1)) hh

theorem source_g2_intersection_ne_bot
    (h : Input KnownSimple.IsKnownSimple H R M K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage K R K ≃* Atlas.G2.Model F) (hq : 4 ≤ Nat.card F) :
    coreCentralIntersectionImage K R ≠ ⊥ := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  have hn := (C27Source.star_intersection_placement_from_source_of_large_order h
    (by rw [Nat.card_congr e.toEquiv]; exact g2_card_large hq)).1.1
  have he := C27Source.component_intersection_star_eq_of_normal_input
    (C27Source.source_join_input h)
  rw [← he] at hn
  intro hb
  have hm := source_simple_equiv_map_intersection h e (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot (by omega))
  rw [hb,Subgroup.map_bot] at hm
  exact hn ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hm.symm)

end CFSG.Quasithin.ChapterC.Section04Constrained

namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section04Constrained
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

@[expose] noncomputable def constrained_g2_simple_equiv
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Atlas.G2.Model F)
    (hF : 4 ≤ Nat.card F) :
    coreCentralQuotient K ≃* Atlas.G2.Model F :=
  (coreCentralQuotientCongr (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
    (source_simple_equiv (h.constrained_source_input K hK hq hout hfK)
      e (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot (by omega)))

theorem constrained_g2_simple_equiv_apply
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Atlas.G2.Model F)
    (hF : 4 ≤ Nat.card F) (k : K) :
    h.constrained_g2_simple_equiv K hK hq hout hfK e hF (coreCentralProjection K k) =
      e (toStarImage (K.map H.subtype) R
        ((K.equivMapOfInjective H.subtype H.subtype_injective) k)) := by
  rw [constrained_g2_simple_equiv,MulEquiv.trans_apply,
    coreCentralQuotientCongr_apply,source_simple_equiv_mk]

theorem constrained_g2_span_rank_le_one
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Atlas.G2.Model F)
    (hF : 4 ≤ Nat.card F) {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H)) ≤ 1 := by
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
    apply source_g2_intersection_ne_bot
      (h.constrained_source_input K hK hq hout hfK) e hF
    rw [←he,hb,Subgroup.map_bot]
  exact (h.constrained_g2_intersection_or_span_rank K hK hq
    (h.constrained_g2_simple_equiv K hK hq hout hfK e hF) hF ho).resolve_left hne

theorem constrained_g2_component_normal
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Atlas.G2.Model F)
    (hF : 4 ≤ Nat.card F) : K.Normal := by
  apply h.constrained_component_normal_of_central_threeRank K hK hq hout hfK
  rw [primeRank_congr 3 (h.constrained_g2_simple_equiv K hK hq hout hfK e hF)]
  exact Atlas.G2.EvenThreeRank.two_le_primeRank

theorem normalizes_of_a5_constrained_g2
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (eA : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Atlas.G2.Model F)
    (hF : 4 ≤ Nat.card F) : M ≤ normalizer (L : Set G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : K.Normal := h.constrained_g2_component_normal K hK hq hout hfK e hF
  exact h.normalizes_of_a5_component_action_fiveRank_le_one eA K
    (h.constrained_span_action_nontrivial K hK hq hout)
    (h.constrained_g2_span_rank_le_one K hK hq hout hfK e hF (by decide : Odd 5))

theorem normalizes_a5_of_constrained_star_g2
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (eA : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hF : 1 < F.degree)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Atlas.G2.Model F.Carrier) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_of_a5_constrained_g2 eA K hK hq hout hfK e
  rw [F.card_eq]
  exact Nat.le_trans (by norm_num : 4 ≤ 2 ^ 2)
    (Nat.pow_le_pow_right (by decide : 0 < 2) hF)

end CFSG.Quasithin.ChapterC.HypothesisC28
