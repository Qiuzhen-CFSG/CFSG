module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.ModelAction
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Compatible descent to the actual PSL₃(4) quotient

An equivalence K/Z(K) ≃ PSL₃(4) specifies a perfect central covering map.
Its induced map on automorphisms is faithful and detects innerness in both
directions: lift a projective conjugating element through the same covering
map and use uniqueness of automorphisms of a perfect central cover. This
also identifies the three-core of each automorphism subgroup with that of
its actual image.

The image of the fixed subgroup upstairs is only proved to lie in the fixed
subgroup downstairs. The fixed inner automorphisms needed by the local
argument are transported from that actual image; surjectivity onto the full
projective fixed subgroup is not assumed. No restriction on Z(K) is made, so
the SL₃(4) exceptional branch and other genuine central covers are retained.

These are transport lemmas for the PSL₃(4) case of Aschbacher--Smith 15.3.38,
printed p.1137, combined manuscript of 1 March 2004. The involution-centralizer
calculations in the projective model and its covers remain separate work.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.PSL3FourAction
variable {K A : Type*} [Group K] [Group A] [Group.IsPerfect K]

/-- The covering map obtained from the specified central-quotient equivalence. -/
@[expose] noncomputable def projectiveCover (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) :
    PerfectCentralCovering.Cover K Matrix.PSL3Four.PSL where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    exact e.injective (hx.trans (map_one e).symm)

/-- This covering has exactly the full center as its kernel. -/
theorem projectiveCover_ker (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) :
    (projectiveCover e).toMonoidHom.ker = center K := by
  apply le_antisymm (projectiveCover e).ker_le_center
  intro x hx
  change e (x : K ⧸ center K) = 1
  rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]

/-- Faithful automorphism descent through the specified covering. -/
noncomputable def projectiveAutMap (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) :
    MulAut K →* MulAut Matrix.PSL3Four.PSL :=
  (projectiveCover e).autMap (projectiveCover_ker e)

/-- The automorphism map commutes with the actual covering projection. -/
theorem projectiveAutMap_apply (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL)
    (a : MulAut K) (x : K) :
    projectiveAutMap e a ((projectiveCover e).toMonoidHom x) =
      (projectiveCover e).toMonoidHom (a x) :=
  (projectiveCover e).autMap_apply (projectiveCover_ker e) a x

/-- Perfectness makes descent faithful, including for nontrivial central covers. -/
theorem projectiveAutMap_injective (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) :
    Function.Injective (projectiveAutMap e) :=
  (projectiveCover e).autMap_injective (projectiveCover_ker e)

/-- Inner automorphisms descend along the same map on group elements. -/
theorem projectiveAutMap_conj (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (x : K) :
    projectiveAutMap e (MulAut.conj x) =
      MulAut.conj ((projectiveCover e).toMonoidHom x) := by
  ext y
  obtain ⟨z, rfl⟩ := (projectiveCover e).surjective y
  rw [projectiveAutMap_apply, MulAut.conj_apply, MulAut.conj_apply,
    map_mul, map_mul, map_inv]

/-- An automorphism of the cover is inner exactly when its descent is inner. -/
theorem projectiveAutMap_mem_inner_iff
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (a : MulAut K) :
    projectiveAutMap e a ∈ MulAut.innerSubgroup Matrix.PSL3Four.PSL ↔
      a ∈ MulAut.innerSubgroup K := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := (projectiveCover e).surjective y
    exact ⟨x, projectiveAutMap_injective e ((projectiveAutMap_conj e x).trans hy)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(projectiveCover e).toMonoidHom x, (projectiveAutMap_conj e x).symm⟩

/-- The actual projective action of the original actor group. -/
@[expose] noncomputable def projectiveAction
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (φ : A →* MulAut K) :
    A →* MulAut Matrix.PSL3Four.PSL := (projectiveAutMap e).comp φ

/-- A faithful action on the perfect cover remains faithful after descent. -/
theorem projectiveAction_injective
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (φ : A →* MulAut K)
    (hφ : Function.Injective φ) : Function.Injective (projectiveAction e φ) :=
  (projectiveAutMap_injective e).comp hφ

/-- Fixed elements map to fixed elements; no converse lifting is asserted. -/
theorem projective_fixedSubgroup_le
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (φ : A →* MulAut K) :
    (fixedSubgroupOfAction φ).map (projectiveCover e).toMonoidHom ≤
      fixedSubgroupOfAction (projectiveAction e φ) := by
  rintro _ ⟨x, hx, rfl⟩ a
  change projectiveAutMap e (φ a) ((projectiveCover e).toMonoidHom x) = _
  rw [projectiveAutMap_apply, hx a]

/-- The projected fixed inner subgroup comes from the image of fixed elements
upstairs, which need not be the entire projective fixed subgroup. -/
theorem projective_fixedInner_image
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (φ : A →* MulAut K) :
    ((fixedSubgroupOfAction φ).map (MulAut.conj : K →* MulAut K)).map
      (projectiveAutMap e) =
    ((fixedSubgroupOfAction φ).map (projectiveCover e).toMonoidHom).map
      (MulAut.conj : Matrix.PSL3Four.PSL →* MulAut Matrix.PSL3Four.PSL) := by
  rw [map_map, map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  exact projectiveAutMap_conj e x


/-- The required inner containment transfers without identifying all fixed
points in the simple quotient. -/
theorem projective_fixedInner_le
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (φ : A →* MulAut K)
    (D : Subgroup (MulAut K))
    (hD : (fixedSubgroupOfAction φ).map (MulAut.conj : K →* MulAut K) ≤ D) :
    ((fixedSubgroupOfAction φ).map (projectiveCover e).toMonoidHom).map
      (MulAut.conj : Matrix.PSL3Four.PSL →* MulAut Matrix.PSL3Four.PSL) ≤
      D.map (projectiveAutMap e) := by
  rw [← projective_fixedInner_image]
  exact map_mono hD

/-- Commuting automorphisms still commute after faithful descent. -/
theorem projective_centralizer_image_le
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (φ : A →* MulAut K)
    (D : Subgroup (MulAut K)) (hD : D ≤ centralizer (φ.range : Set (MulAut K))) :
    D.map (projectiveAutMap e) ≤
      centralizer ((projectiveAction e φ).range : Set (MulAut Matrix.PSL3Four.PSL)) := by
  rintro _ ⟨d, hd, rfl⟩ _ ⟨a, rfl⟩
  exact (map_mul (projectiveAutMap e) (φ a) d).symm.trans
    ((congrArg (projectiveAutMap e) (hD hd (φ a) ⟨a, rfl⟩)).trans
      (map_mul (projectiveAutMap e) d (φ a)))

/-- Three-core triviality is equivalent for a subgroup and its actual
projective automorphism image. -/
theorem projective_threeCore_eq_bot_iff
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) (D : Subgroup (MulAut K)) :
    pCore 3 (D.map (projectiveAutMap e)) = ⊥ ↔ pCore 3 D = ⊥ := by
  let d := D.equivMapOfInjective (projectiveAutMap e) (projectiveAutMap_injective e)
  rw [← pCore_map_iso 3 d]
  exact (pCore 3 D).map_eq_bot_iff_of_injective d.injective
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.PSL3FourAction
