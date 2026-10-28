module
public import CFSG.Quasithin.ChapterC.Section04.A5LinearThreeNormality

/-!
# Odd ranks of the constrained linear-three action

The perfect action on the component central quotient preserves the literal
nontrivial radical intersection. Its two-local normalizer lies in a point
or line parabolic of PSL₃. The perfect residual of either parabolic is an
extension of SL₂ by a two-group, so every odd prime rank is at most one.
This extends the existing quintic argument to the cubic rank needed by
the unitary residual, without discarding the special-linear scalar kernel.

Source: Aschbacher–Smith C.4.5–8, pp.152–154, in the original
4.2.12–13 pushing-up argument, pp.610–612.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.OrdinaryPlacement.SL3Local
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every perfect subgroup of a binary PSL₃ two-local has odd rank at most one. -/
theorem no_perfect_odd_rank_two_in_two_normalizer
    (P : Subgroup PSL(3,F)) (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : 2 ≤ primeRank p A)
    (hF : 4 ≤ Nat.card F) (f : A →* PSL(3,F)) (hf : Function.Injective f)
    (hn : f.range ≤ normalizer (P : Set PSL(3,F))) : False := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n,_,hcard⟩ := FiniteField.card F 2
  have hcardF : Nat.card F = 2 ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨g,point,hg⟩ :=
    MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F n.pos hcardF
      (normalizer (P : Set PSL(3,F))) ⟨P,hne,hp,rfl⟩
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hj : j.range ≤ Matrix.PSL3.RootPlaneGeometry.parabolic F point := by
    refine le_trans ?_ hg
    rintro _ ⟨a,rfl⟩
    exact mem_map_of_mem _ (hn ⟨a,rfl⟩)
  apply Matrix.PSL3.LinearThree.PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic F
    ho hr hF j ((MulAut.conj g).injective.comp hf)
  cases point
  · exact Or.inr hj
  · exact Or.inl hj
end CFSG.Quasithin.ChapterC.OrdinaryPlacement.SL3Local

namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

theorem constrained_linear_three_intersection_or_odd_rank
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : coreCentralQuotient K ≃* PSL(3,F)) (hF : 4 ≤ Nat.card F)
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
  have hb : primeRank p B' ≤ 1 := by
    by_contra! hb
    apply OrdinaryPlacement.SL3Local.no_perfect_odd_rank_two_in_two_normalizer
      P (hU.map e.toMonoidHom) hP ho (by omega) hF f hf
    rintro _ ⟨a,rfl⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hconj a]
    exact coreCentralActorImage_map_stabilizes K A (R.subgroupOf H) hAR e a.property
  exact (primeRank_equiv p (B.equivMapOfInjective (MulAut.congr e).toMonoidHom
    (MulAut.congr e).injective)).le.trans hb
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource Section04Constrained

theorem constrained_linear_three_span_oddRank_le_one
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(3,F))
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
    apply source_linear_three_intersection_ne_bot
      (h.constrained_source_input K hK hq hout hfK) e hF
    rw [←he,hb,Subgroup.map_bot]
  exact (h.constrained_linear_three_intersection_or_odd_rank K hK hq
    (h.constrained_linear_three_simple_equiv K hK hq hout hfK e) hF ho).resolve_left hne

end CFSG.Quasithin.ChapterC.HypothesisC28
