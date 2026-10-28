module
public import Theory.GroupTheory.PerfectCentralCoverActions
public import Theory.GroupTheory.PCoreNormalizerAction
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarNormalizerAction
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels

/-!
# The literal core-to-star comparison of normalizer actions

Actors normalizing both the component and radical act on the C.2.7 star
image. The core-to-star map is an equivariant perfect central cover. It
therefore preserves action kernels, orders and innerness, including the
order in the outer automorphism group. Its prime-to-five kernel also
preserves five-rank. No quotient centralization is lifted to ordinary
centralization in the ambient group.

Source: Aschbacher--Smith C.2.7, printed pp.145--147. The actual marked
application in 14.6.15 is SourceComponent.StarComparison.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] (K R : Subgroup G)

/-- Conjugation by the common normalizer on the literal star component. -/
noncomputable def starComponentAction :
    (normalizer (K : Set G) ⊓ normalizer (R : Set G) : Subgroup G) →*
      MulAut (starImage K R K) where
  toFun g := starComponentAut K R g g.property.1 g.property.2
  map_one' := by
    apply MulEquiv.ext
    intro y
    obtain ⟨k,rfl⟩ := toStarImage_surjective K R y
    rw [starComponentAut_toStarImage]
    change toStarImage K R (K.normalizerMonoidHom 1 k) = toStarImage K R k
    rw [map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro y
    obtain ⟨k,rfl⟩ := toStarImage_surjective K R y
    change starComponentAut K R _ _ _ (toStarImage K R k) =
      starComponentAut K R _ _ _ (starComponentAut K R _ _ _ (toStarImage K R k))
    rw [starComponentAut_toStarImage,starComponentAut_toStarImage,starComponentAut_toStarImage]
    congr 1
    apply Subtype.ext
    change ((g : G) * h) * (k : G) * ((g : G) * h)⁻¹ =
      (g : G) * ((h : G) * k * (h : G)⁻¹) * (g : G)⁻¹
    group

theorem starComponentAction_apply
    (g : (normalizer (K : Set G) ⊓ normalizer (R : Set G) : Subgroup G))
    (x : starImage K R K) :
    starComponentAction K R g x = starComponentAut K R g g.property.1 g.property.2 x := by rfl

/-- For an actor lying in the original component, the star action is
conjugation by its literal image. -/
theorem starComponentAction_on_component
    (g : (normalizer (K : Set G) ⊓ normalizer (R : Set G) : Subgroup G))
    (hg : (g : G) ∈ K) :
    starComponentAction K R g = MulAut.conj (toStarImage K R ⟨g,hg⟩) := by
  ext y
  obtain ⟨k,rfl⟩ := toStarImage_surjective K R y
  rw [starComponentAction_apply,starComponentAut_toStarImage,MulAut.conj_apply,
    ←map_inv,←map_mul,←map_mul]
  rfl

variable {K R}
theorem coreToStar_equivariant_starComponentAction
    (hR : R ≤ normalizer (K : Set G))
    (g : (normalizer (K : Set G) ⊓ normalizer (R : Set G) : Subgroup G))
    (x : K ⧸ pCore 2 K) :
    coreToStar hR (pCoreNormalizerAction 2 K (inclusion inf_le_left g) x) =
      starComponentAction K R g (coreToStar hR x) := by
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
  rw [pCoreNormalizerAction_mk,coreToStar_mk,coreToStar_mk,
    starComponentAction_apply,starComponentAut_toStarImage]
  rfl

variable [Finite G] {H M : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K)

private noncomputable def coreToStarCover :
    PerfectCentralCovering.Cover (K ⧸ pCore 2 K) (starImage K R K) where
  toMonoidHom := coreToStar h.normalizes
  surjective := coreToStar_surjective h.normalizes
  isPerfect := by
    let := h.quasisimple
    infer_instance
  ker_le_center := coreToStar_ker_central_from_source h

include h

theorem starComponentAction_ker :
    (starComponentAction K R).ker =
      ((pCoreNormalizerAction 2 K).comp (inclusion inf_le_left)).ker :=
  ((coreToStarCover h).equivariantActions_ker
    ((pCoreNormalizerAction 2 K).comp (inclusion inf_le_left))
    (starComponentAction K R) (coreToStar_equivariant_starComponentAction h.normalizes)).symm

theorem starComponentAction_order
    (g : (normalizer (K : Set G) ⊓ normalizer (R : Set G) : Subgroup G)) :
    orderOf (starComponentAction K R g) =
      orderOf (pCoreNormalizerAction 2 K (inclusion inf_le_left g)) :=
  ((coreToStarCover h).equivariantActions_order
    ((pCoreNormalizerAction 2 K).comp (inclusion inf_le_left))
    (starComponentAction K R) (coreToStar_equivariant_starComponentAction h.normalizes) g).symm

theorem starComponentAction_inner_iff
    (g : (normalizer (K : Set G) ⊓ normalizer (R : Set G) : Subgroup G)) :
    starComponentAction K R g ∈ MulAut.innerSubgroup (starImage K R K) ↔
      pCoreNormalizerAction 2 K (inclusion inf_le_left g) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K) :=
  ((coreToStarCover h).equivariant_inner_iff _ _
    (coreToStar_equivariant_starComponentAction h.normalizes g)).symm

theorem starComponentAction_outer_ker :
    ((QuotientGroup.mk' (MulAut.innerSubgroup (starImage K R K))).comp
      (starComponentAction K R)).ker =
      ((pCoreNormalizerOuterAction 2 K).comp (inclusion inf_le_left)).ker :=
  ((coreToStarCover h).equivariantActions_outer_ker
    ((pCoreNormalizerAction 2 K).comp (inclusion inf_le_left))
    (starComponentAction K R) (coreToStar_equivariant_starComponentAction h.normalizes)).symm

theorem starComponentAction_outer_order
    (g : (normalizer (K : Set G) ⊓ normalizer (R : Set G) : Subgroup G)) :
    orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (starImage K R K))
      (starComponentAction K R g)) =
      orderOf (pCoreNormalizerOuterAction 2 K (inclusion inf_le_left g)) :=
  ((coreToStarCover h).equivariantActions_outer_order
    ((pCoreNormalizerAction 2 K).comp (inclusion inf_le_left))
    (starComponentAction K R) (coreToStar_equivariant_starComponentAction h.normalizes) g).symm
/-- The literal star map preserves five-rank, not merely five-divisibility. -/
theorem starImage_five_rank_from_source :
    primeRank 5 (starImage K R K) = primeRank 5 K := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact (primeRank_eq_of_surjective_of_coprime 5 (toStarImage K R)
    (toStarImage_surjective K R)
    ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr
      (toStarImage_ker_not_five_from_source h))).symm

end CFSG.Quasithin.ChapterC.C27Source
