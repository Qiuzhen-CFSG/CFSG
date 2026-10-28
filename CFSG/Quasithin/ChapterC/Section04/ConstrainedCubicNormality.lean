module
public import Theory.GroupTheory.CComponent.CubicCenterRankNormal
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedParabolic

/-!
# Cubic-rank normality for the literal constrained source component

The actual C.2.7 source bounds the center of K/O₂(K) by three. Hence a
cubic-rank lower bound of two makes the selected C-component normal in H.
The lower bound may also be supplied on its central quotient: odd rank
one gives cyclic Sylow subgroups and persists under the literal quotient.

Source: Aschbacher–Smith A.3.6, C.2.7(1) and C.4.5, pp.43–45,145,152.
This is used by the remaining finite constrained rows of the A₅ C.4.8
normality argument.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
theorem constrained_component_normal_of_core_threeRank
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K)) : K.Normal := by
  let := hq
  let eK := K.equivMapOfInjective H.subtype H.subtype_injective
  let e := QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  have hc := C27Source.coreQuotient_center_card_from_source
    (h.constrained_source_input K hK hq hout hfK)
  have hz : Nat.card (center (K ⧸ pCore 2 K)) ≤ 3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    rcases hc with hc | hc <;> omega
  exact hK.normal_of_cubic_core_center_threeRank hz hr
    (h.sqtk.stronglyQuasithin 3 (by decide) (by decide))

/-- Odd rank two on the literal central quotient already forces normality. -/
theorem constrained_component_normal_of_central_threeRank
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (hr : 2 ≤ primeRank 3 (coreCentralQuotient K)) : K.Normal := by
  apply h.constrained_component_normal_of_core_threeRank K hK hq hout hfK
  by_contra! hlt
  let P : Sylow 3 (K ⧸ pCore 2 K) := Classical.choice inferInstance
  have hc := P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega :
    primeRank 3 (K ⧸ pCore 2 K) ≤ 1)
  have hh := P.primeRank_quotient_le_one hc (center (K ⧸ pCore 2 K))
  change primeRank 3 (coreCentralQuotient K) ≤ 1 at hh
  omega

/-- The actual C.2.7 central cover identifies the two central quotients. -/
@[expose] noncomputable def constrained_star_central_equiv
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) :
    coreCentralQuotient K ≃*
      (starImage (K.map H.subtype) R (K.map H.subtype) ⧸
        center (starImage (K.map H.subtype) R (K.map H.subtype))) := by
  let s := h.constrained_source_input K hK hq hout hfK
  let := s.quasisimple
  let c : PerfectCentralCovering.Cover
      ((K.map H.subtype) ⧸ pCore 2 (K.map H.subtype))
      (starImage (K.map H.subtype) R (K.map H.subtype)) :=
    { toMonoidHom := coreToStar s.normalizes
      surjective := coreToStar_surjective s.normalizes
      isPerfect := inferInstance
      ker_le_center := C27Source.coreToStar_ker_central_from_source s }
  exact (coreCentralQuotientCongr
    (K.equivMapOfInjective H.subtype H.subtype_injective)).trans c.quotientCenterEquiv

/-- Use the displayed central quotient of the original star image. -/
theorem constrained_component_normal_of_star_central_threeRank
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (hr : 2 ≤ primeRank 3
      (starImage (K.map H.subtype) R (K.map H.subtype) ⧸
        center (starImage (K.map H.subtype) R (K.map H.subtype)))) : K.Normal := by
  apply h.constrained_component_normal_of_central_threeRank K hK hq hout hfK
  rwa [primeRank_congr 3 (h.constrained_star_central_equiv K hK hq hout hfK)]
end CFSG.Quasithin.ChapterC.HypothesisC28
