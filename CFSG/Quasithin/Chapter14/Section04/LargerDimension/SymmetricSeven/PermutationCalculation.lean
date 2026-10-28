module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven.Catalogue
public import Theory.SpecificGroups.SymmetricSeven.ResidualTripleGeometry

/-!
# The permutation calculations for Lemma 14.4.11

The literal pointwise stabilizers have the same embedded residuals as the
catalogue's first two overgroups. Residual-lift uniqueness therefore identifies
the source actors, even for a nonsplit two-group kernel. The actual permutation
overlap quotient supplies S₃ × S₃ and retains the equation on quotient maps.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 14.4.11 and the first paragraph of its proof, printed p.1011.
-/

@[expose] public section
open Subgroup
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven
namespace PermutationCalculation
open Theory.SpecificGroups.SymmetricSeven
variable {A : Type*} [Group A] [Finite A]

theorem firstActor_eq_pointwise_lift (q : A →* S7) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) :
    firstActor q = residualLift q ResidualTripleGeometry.fourFixer :=
  residualLift_eq_of_residual_eq q hq hk ResidualTripleGeometry.residual_fourFixer.symm

theorem secondActor_eq_pointwise_lift (q : A →* S7) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) :
    secondActor q = residualLift q ResidualTripleGeometry.threeFixer :=
  residualLift_eq_of_residual_eq q hq hk ResidualTripleGeometry.residual_threeFixer.symm

omit [Finite A] in
/-- The source Sylow image preserves the literal four, two and one point blocks. -/
theorem sourceSylow_preserves_blocks (q : A →* S7) (T : Subgroup A)
    (hT : T.map q = standardTwo) (t : A) (ht : t ∈ T) :
    ({2,3,4,5} : Finset (Fin 7)).image (q t) = {2,3,4,5} ∧
    ({0,1} : Finset (Fin 7)).image (q t) = {0,1} ∧ q t 6 = 6 :=
  ResidualTripleGeometry.standardTwo_preserves_blocks (q t)
    (hT ▸ mem_map_of_mem q ht)

omit [Finite A] in
/-- Relative normality in the partition preimage and order eight of the image
identify the source normal eight-group with the three pair swaps. -/
theorem normal_eight_image_eq_B8 (q : A →* S7) (hq : Function.Surjective q)
    (N : Subgroup A) (hN : N ≤ synthemeOvergroup.comap q)
    [(N.subgroupOf (synthemeOvergroup.comap q)).Normal]
    (h8 : Nat.card (N.map q) = 8) : N.map q = ResidualTripleGeometry.B8 := by
  apply ResidualTripleGeometry.normal_eight_eq_B8 _ (map_le_iff_le_comap.mpr hN) _ h8
  have hn := le_normalizer_of_normal_subgroupOf hN
  have hm := (map_mono (f := q) hn).trans (le_normalizer_map q)
  rwa [map_comap_eq_self_of_surjective hq] at hm

/-- The quotient of the lifted overlap, with its literal projection to S₇. -/
noncomputable def sourceOverlapQuotientEquiv (q : A →* S7) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (T : Subgroup A) (hT : T.map q = standardTwo) :
    coreQuotient (firstActor q ⊔ secondActor q ⊔ T) ≃*
      (ResidualTripleGeometry.S3 × ResidualTripleGeometry.S3) :=
  (overlapQuotientEquiv q hq hk T hT).trans ResidualTripleGeometry.overlapQuotientEquiv

/-- The resulting isomorphism uses precisely the original quotient projection. -/
theorem sourceOverlapQuotientEquiv_mk (q : A →* S7) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (T : Subgroup A) (hT : T.map q = standardTwo)
    (x : (firstActor q ⊔ secondActor q ⊔ T : Subgroup A)) :
    sourceOverlapQuotientEquiv q hq hk T hT
      (QuotientGroup.mk' (pCore 2 (firstActor q ⊔ secondActor q ⊔ T : Subgroup A)) x) =
    ResidualTripleGeometry.overlapProjection ⟨q x.val, by
      change q x.val ∈ modelOverlap
      rw [← overlap_map q hq T hT]
      exact mem_map_of_mem q x.property⟩ := by
  let f := MulEquiv.subgroupCongr (overlap_map q hq T hT)
  change ResidualTripleGeometry.overlapQuotientEquiv
    (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
      (coreImageEquiv q hk _ (QuotientGroup.mk' _ x))) = _
  rw [coreImageEquiv_mk]
  erw [QuotientGroup.congr_mk']
  exact ResidualTripleGeometry.overlapQuotientEquiv_mk _

end PermutationCalculation
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven
