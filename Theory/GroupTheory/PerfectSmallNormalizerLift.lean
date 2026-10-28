module

public import Theory.GroupTheory.PerfectSmallNormalizer
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Lifting normalization through a solvable kernel of small relative index

A perfect subgroup A normalized modulo a solvable kernel is normalized before
quotienting if its normalizer has index at most four in a subgroup containing
that kernel. The small-index theorem first makes A normal in A ker(f).
It is then the solvable residual of this join, so normalization of the image
lifts through the characteristic residual.

This is the group-theoretic step in Aschbacher--Smith, Lemma 12.6.5,
printed p.824 (combined manuscript of 1 March 2004). In that application
f is the actual quotient of K_v S by its two-core.
-/

public section

open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D]

/-- Lift image normalization without assuming that the kernel normalizes A. -/
theorem le_normalizer_of_perfect_image_of_small_kernel
    (f : G →* D) (A R : Subgroup G) [Group.IsPerfect A]
    [Group.IsSolvable f.ker] (hkR : f.ker ≤ R)
    (hi : (normalizer (A : Set G)).relIndex R ≤ 4)
    (himage : R.map f ≤ normalizer (A.map f : Set D)) :
    R ≤ normalizer (A : Set G) := by
  let P := A ⊔ f.ker
  have hAP : A ≤ P := le_sup_left
  have hkerP : f.ker ≤ P := le_sup_right
  let : (A.subgroupOf P).Normal :=
    normal_in_sup_of_perfect_of_solvable_of_small_normalizer A f.ker
      (by rw [normalizer_eq_top]; exact le_top)
      ((relIndex_le_of_le_right (H := normalizer (A : Set G)) hkR index_ne_zero_of_finite).trans hi)
  let : Group.IsPerfect (A.subgroupOf P) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hAP).symm.toMonoidHom)
      (subgroupOfEquivOfLe hAP).symm.surjective
  let : (f.ker.subgroupOf P).Normal := inferInstance
  let : Group.IsSolvable (f.ker.subgroupOf P) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hkerP).toMonoidHom)
      (subgroupOfEquivOfLe hkerP).injective
  have he : (solvableResidual P).map P.subtype = A := by
    have h := (inferInstance : (A.subgroupOf P).Normal).isSubnormal.eq_solvableResidual_of_sup_eq_top
      (f.ker.subgroupOf P) (codisjoint_subgroupOf_sup A f.ker).eq_top
    rw [← h, map_subgroupOf_eq_of_le hAP]
  have hRP : R ≤ normalizer (P : Set G) := by
    have h := map_le_iff_le_comap.mp himage
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _), comap_map_eq] at h
    exact h
  have h := hRP.trans (normalizer_le_normalizer_characteristic_image P (solvableResidual P))
  rwa [he] at h
end Subgroup
