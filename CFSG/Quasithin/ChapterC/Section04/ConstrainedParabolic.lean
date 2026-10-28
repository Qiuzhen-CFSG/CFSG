module
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedAction
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectTwoNormalizer
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Theory.GroupTheory.CComponent.CenterlessRankNormal
/-!
# The constrained symplectic parabolic obstruction in C.4

The original C.2.7 star marking identifies the component's central core
quotient with the actual symplectic matrix group. Its large-order placement
forces the image of R intersect K to be nontrivial. The perfect conjugate
span stabilizes that literal image, so its automorphism image has odd-prime
rank at most one by the two-local parabolic theorem.

The trivial even symplectic multiplier also identifies the whole two-core
quotient. Its cubic rank two forces the selected C-component to be normal.
These results use the genuine C.2.8 and constrained escaping-component data;
no assumed C.2.7 classification interface or actor faithfulness is added.
The imported action theorem also supplies nontriviality of this exact image.
The remaining original-pair consumer must show that both A5 factors survive
in it before using the rank bound.

Source: Aschbacher--Smith C.4.5--7, printed pp.152--153, using C.2.7(1--3).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section04Constrained
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {H M K R : Subgroup G}

@[expose] noncomputable def source_simple_equiv
    (h : Input KnownSimple.IsKnownSimple H R M K)
    {D : Type*} [Group D] (e : starImage K R K ≃* D) (hz : center D = ⊥) :
    coreCentralQuotient K ≃* D := by
  let := h.quasisimple
  let f := e.toMonoidHom.comp (coreToStar h.normalizes)
  have hker : f.ker = (coreToStar h.normalizes).ker :=
    MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective
  let c : PerfectCentralCovering.Cover (K ⧸ pCore 2 K) D :=
    { toMonoidHom := f
      surjective := e.surjective.comp (coreToStar_surjective h.normalizes)
      isPerfect := inferInstance
      ker_le_center := hker ▸ C27Source.coreToStar_ker_central_from_source h }
  have hc : f.ker = center (K ⧸ pCore 2 K) := by
    simpa only [hz,MonoidHom.comap_bot] using c.comap_center
  exact (QuotientGroup.quotientMulEquivOfEq hc.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f c.surjective)

theorem source_simple_equiv_mk
    (h : Input KnownSimple.IsKnownSimple H R M K)
    {D : Type*} [Group D] (e : starImage K R K ≃* D) (hz : center D = ⊥) (k : K) :
    source_simple_equiv h e hz (coreCentralProjection K k) = e (toStarImage K R k) := rfl


end CFSG.Quasithin.ChapterC.Section04Constrained

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

theorem constrained_symplectic_intersection_or_span_rank
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : coreCentralQuotient K ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
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
  let D := Theory.SpecificGroups.SymplecticFour.Sp F
  let P := U.map e.toMonoidHom
  let B' := B.map (MulAut.congr e).toMonoidHom
  have hP : P ≠ ⊥ := fun hp => hu ((U.map_eq_bot_iff_of_injective e.injective).mp hp)
  let : Group.IsPerfect B' := Group.IsPerfect.map _
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  let : Group.IsSolvable (MulAut.Outer D) :=
    MulAut.isSolvable_outer_of_mulEquiv e.symm
  have hb := Theory.SpecificGroups.SymplecticFour.perfect_automorphism_stabilizer_odd_rank_le_one
    P (hU.map e.toMonoidHom) hP B'
    (coreCentralActorImage_map_stabilizes K A (R.subgroupOf H) hAR e) ho
  exact (primeRank_equiv p (B.equivMapOfInjective (MulAut.congr e).toMonoidHom
    (MulAut.congr e).injective)).le.trans hb
end CFSG.Quasithin.ChapterC.HypothesisC28

namespace CFSG.Quasithin.ChapterC.Section04Constrained
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {H M K R : Subgroup G}

theorem source_simple_equiv_map_intersection
    (h : Input KnownSimple.IsKnownSimple H R M K)
    {D : Type*} [Group D] (e : starImage K R K ≃* D) (hz : center D = ⊥) :
    (coreCentralIntersectionImage K R).map (source_simple_equiv h e hz).toMonoidHom =
      ((R.subgroupOf K).map (toStarImage K R)).map e.toMonoidHom := by
  rw [coreCentralIntersectionImage,map_map,map_map]
  congr 1

theorem source_symplectic_intersection_ne_bot
    (h : Input KnownSimple.IsKnownSimple H R M K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage K R K ≃* Sp F) (hq : 4 ≤ Nat.card F) :
    coreCentralIntersectionImage K R ≠ ⊥ := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  have hn := (C27Source.star_symplectic_radical_placement
    (C27Source.source_join_input h) e hq).1.1
  have he := C27Source.component_intersection_star_eq_of_normal_input
    (C27Source.source_join_input h)
  rw [← he] at hn
  intro hb
  have hm := source_simple_equiv_map_intersection h e (EvenProjective.center_eq_bot (F := F))
  rw [hb,Subgroup.map_bot] at hm
  exact hn ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hm.symm)

end CFSG.Quasithin.ChapterC.Section04Constrained

namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section04Constrained Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

@[expose] noncomputable def constrained_symplectic_simple_equiv
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Sp F) :
    coreCentralQuotient K ≃* Sp F :=
  (coreCentralQuotientCongr (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
    (source_simple_equiv (h.constrained_source_input K hK hq hout hfK)
      e (EvenProjective.center_eq_bot (F := F)))

theorem constrained_symplectic_simple_equiv_apply
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Sp F) (k : K) :
    h.constrained_symplectic_simple_equiv K hK hq hout hfK e (coreCentralProjection K k) =
      e (toStarImage (K.map H.subtype) R
        ((K.equivMapOfInjective H.subtype H.subtype_injective) k)) := by
  rw [constrained_symplectic_simple_equiv,MulEquiv.trans_apply,
    coreCentralQuotientCongr_apply,source_simple_equiv_mk]

theorem constrained_symplectic_span_rank_le_one
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Sp F)
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
    apply source_symplectic_intersection_ne_bot
      (h.constrained_source_input K hK hq hout hfK) e hF
    rw [←he,hb,Subgroup.map_bot]
  exact (h.constrained_symplectic_intersection_or_span_rank K hK hq
    (h.constrained_symplectic_simple_equiv K hK hq hout hfK e) ho).resolve_left hne

theorem constrained_symplectic_component_normal
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Sp F)
    (hF : 4 ≤ Nat.card F) : K.Normal := by
  let := hq
  let ec := h.constrained_symplectic_simple_equiv K hK hq hout hfK e
  have hz := PerfectCentralCovering.center_eq_bot_of_centralQuotientEquiv
    (CentralCovers.Even.universalProjection_ker_eq_bot (by omega : 3 < Nat.card F)) ec
  let ew := PerfectCentralCovering.centralQuotientEquivOfUniversalKernelEqBot
    (CentralCovers.Even.universalProjection_ker_eq_bot (by omega : 3 < Nat.card F)) ec
  apply hK.normal_of_centerless_core_threeRank hz
  · rw [primeRank_congr 3 ew]
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Sp F)).subtype (commutator (Sp F)).subtype_injective)
  · exact h.sqtk.stronglyQuasithin 3 (by decide) (by decide)

end CFSG.Quasithin.ChapterC.HypothesisC28
