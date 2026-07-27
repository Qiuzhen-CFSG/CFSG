import Submission.ZStar.SubgroupBrauerMap

/-!
# Transitivity of coefficient Brauer restriction

The subgroup Brauer calculation is additive without hypotheses.  When a
subgroup `Q` of an involution centralizer is admissible, its centralizer in
the ambient group is canonically the same as its centralizer inside that
involution centralizer.  This file records the resulting coefficientwise
transitivity.  No block-correspondence conclusion is used here.
-/

noncomputable section

namespace Submission.ZStar
namespace BrauerTransitivity

universe u v

attribute [local instance] Fintype.ofFinite

open Subgroup

/-! The centralizer equivalence used to compare the two target group
algebras. -/

noncomputable def centralizerMapEquiv
    {G : Type v} [Group G]
    (H : Subgroup G) (Q : Subgroup H)
    (hC : Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G) ≤ H) :
    Subgroup.centralizer (Q : Set H) ≃* 
      Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G) := by
  let K : Subgroup G := Q.map H.subtype
  let C : Subgroup H := Subgroup.centralizer (Q : Set H)
  let D : Subgroup G := Subgroup.centralizer (K : Set G)
  exact
    { toFun := fun x =>
        ⟨(x : G), by
          rw [Subgroup.mem_centralizer_iff]
          intro q hq
          obtain ⟨qH, hqH, rfl⟩ := Subgroup.mem_map.mp hq
          exact congrArg Subtype.val
            (Subgroup.mem_centralizer_iff.mp x.property qH hqH)
          ⟩
      invFun := fun y =>
        ⟨⟨(y : G), hC y.property⟩, by
          rw [Subgroup.mem_centralizer_iff]
          intro q hq
          have hqK : (q : G) ∈ K := by
            exact Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
          apply Subtype.ext
          exact Subgroup.mem_centralizer_iff.mp y.property (q : G) hqK
          ⟩
      left_inv := by intro x; rfl
      right_inv := by intro y; rfl
      map_mul' := by intro x y; rfl }

@[simp] theorem centralizerMapEquiv_apply_coe
    {G : Type v} [Group G]
    (H : Subgroup G) (Q : Subgroup H)
    (hC : Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G) ≤ H)
    (x : Subgroup.centralizer (Q : Set H)) :
    ((centralizerMapEquiv H Q hC x :
      Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G)) : G) = (x : G) := rfl

@[simp] theorem centralizerMapEquiv_symm_apply_coe
    {G : Type v} [Group G]
    (H : Subgroup G) (Q : Subgroup H)
    (hC : Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G) ≤ H)
    (y : Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G)) :
    ((centralizerMapEquiv H Q hC).symm y : H) =
      ⟨(y : G), hC y.property⟩ := rfl

/-! The corresponding statement for a local element embedded into the
ambient group algebra. -/

theorem mapDomain_subgroupRestriction_eq_subgroupRestriction_mapDomain
    {R : Type u} {G : Type v} [Semiring R] [Group G]
    (H : Subgroup G) (Q : Subgroup H)
    (hC : Subgroup.centralizer
        ((Q.map H.subtype : Subgroup G) : Set G) ≤ H)
    (e : MonoidAlgebra R H) :
    MonoidAlgebra.mapDomainRingHom R
        (centralizerMapEquiv H Q hC).toMonoidHom
        (DefectSupport.subgroupCentralizerRestriction R Q e) =
      DefectSupport.subgroupCentralizerRestriction R
        (Q.map H.subtype : Subgroup G)
        (MonoidAlgebra.mapDomainRingHom R H.subtype e) := by
  ext y
  let E := centralizerMapEquiv H Q hC
  let x : Subgroup.centralizer (Q : Set H) := E.symm y
  have hy : y = E x := by
    exact (E.apply_symm_apply y).symm
  rw [hy]
  change Finsupp.mapDomain E
      (DefectSupport.subgroupCentralizerRestriction R Q e) (E x) =
    (MonoidAlgebra.mapDomainRingHom R H.subtype e) ((E x : _) : G)
  rw [Finsupp.mapDomain_apply E.injective]
  change e (x : H) = Finsupp.mapDomain H.subtype e (x : G)
  exact (Finsupp.mapDomain_apply H.subtype_injective e (x : H)).symm

/-! For an involution centralizer, the preceding comparison also identifies
the iterated restriction of an ambient element with its direct subgroup
restriction. -/

theorem mapDomain_iteratedCentralizerRestriction_eq_subgroupRestriction
    {R : Type u} {G : Type v} [Semiring R] [Group G]
    (z : G)
    (Q : Subgroup (Subgroup.centralizer ({z} : Set G)))
    (hC : Subgroup.centralizer
        ((Q.map (Subgroup.centralizer ({z} : Set G)).subtype :
          Subgroup G) : Set G) ≤
      Subgroup.centralizer ({z} : Set G))
    (e : MonoidAlgebra R G) :
    MonoidAlgebra.mapDomainRingHom R
        (centralizerMapEquiv
          (Subgroup.centralizer ({z} : Set G)) Q hC).toMonoidHom
        (DefectSupport.subgroupCentralizerRestriction R Q
          (BrauerMapScratch.centralizerRestriction R z e)) =
      DefectSupport.subgroupCentralizerRestriction R
        (Q.map (Subgroup.centralizer ({z} : Set G)).subtype : Subgroup G) e := by
  let H : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let E := centralizerMapEquiv H Q hC
  ext y
  let x : Subgroup.centralizer (Q : Set H) := E.symm y
  have hy : y = E x := (E.apply_symm_apply y).symm
  rw [hy]
  change Finsupp.mapDomain E
      (DefectSupport.subgroupCentralizerRestriction R Q
        (BrauerMapScratch.centralizerRestriction R z e)) (E x) = e (x : G)
  rw [Finsupp.mapDomain_apply E.injective]
  rfl

theorem mapDomainRingEquiv_mem_center
    {R : Type u} {M : Type v} {N : Type*}
    [Semiring R] [Monoid M] [Monoid N]
    (E : M ≃* N) (e : MonoidAlgebra R M)
    (he : e ∈ Set.center (MonoidAlgebra R M)) :
    MonoidAlgebra.mapDomainRingEquiv R E e ∈
      Set.center (MonoidAlgebra R N) := by
  apply Semigroup.mem_center_iff.mpr
  intro a
  let a' := (MonoidAlgebra.mapDomainRingEquiv R E).symm a
  have hcomm := Semigroup.mem_center_iff.mp he a'
  have hcomm' := congrArg (MonoidAlgebra.mapDomainRingEquiv R E) hcomm
  rw [map_mul, map_mul] at hcomm'
  change
    (MonoidAlgebra.mapDomainRingEquiv R E)
          ((MonoidAlgebra.mapDomainRingEquiv R E).symm a) *
        (MonoidAlgebra.mapDomainRingEquiv R E) e =
      (MonoidAlgebra.mapDomainRingEquiv R E) e *
        (MonoidAlgebra.mapDomainRingEquiv R E)
          ((MonoidAlgebra.mapDomainRingEquiv R E).symm a) at hcomm'
  have ha :
      (MonoidAlgebra.mapDomainRingEquiv R E)
          ((MonoidAlgebra.mapDomainRingEquiv R E).symm a) = a := by
    exact (MonoidAlgebra.mapDomainRingEquiv R E).apply_symm_apply a
  rw [ha] at hcomm'
  exact hcomm'

theorem mapDomainRingEquiv_isIdempotent
    {R : Type u} {M : Type v} {N : Type*}
    [Semiring R] [Monoid M] [Monoid N]
    (E : M ≃* N) (e : MonoidAlgebra R M)
    (he : IsIdempotentElem e) :
    IsIdempotentElem (MonoidAlgebra.mapDomainRingEquiv R E e) := by
  exact he.map (MonoidAlgebra.mapDomainRingEquiv R E)

theorem mapDomainRingEquiv_ne_zero
    {R : Type u} {M : Type v} {N : Type*}
    [Semiring R] [Monoid M] [Monoid N]
    (E : M ≃* N) (e : MonoidAlgebra R M)
    (he : e ≠ 0) :
    MonoidAlgebra.mapDomainRingEquiv R E e ≠ 0 := by
  intro hzero
  apply he
  exact (MonoidAlgebra.mapDomainRingEquiv R E).injective hzero

theorem augmentation_mapDomainRingEquiv
    {R : Type u} {M : Type v} {N : Type*}
    [CommRing R] [Monoid M] [Monoid N]
    (E : M ≃* N) (e : MonoidAlgebra R M) :
    AugmentationScratch.augmentation R N
        (MonoidAlgebra.mapDomainRingEquiv R E e) =
      AugmentationScratch.augmentation R M e := by
  induction e using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single m r =>
      simp [MonoidAlgebra.mapDomainRingEquiv_single,
        AugmentationScratch.augmentation_single]

end BrauerTransitivity
end Submission.ZStar
