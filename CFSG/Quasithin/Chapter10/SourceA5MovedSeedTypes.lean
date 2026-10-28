module
public import CFSG.Quasithin.Chapter10.SourceA5ProductTypeAlternatives
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductQuotient
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Normalizer
public import Theory.Representation.BinaryOffender.Homogeneous.QuotientTwist
/-!
# Product types of the original moved seed

The original irreducible central-image seed factors through the literal
marked quotient L₀/O₂(L₀) ≅ A₅ × A₅. The deleted tensor square is invariant
under every automorphism of that product; homogeneity would therefore make
the seed stable under T and equal to the whole local module. A proper seed
has only the natural or mixed alternatives.

Source: Aschbacher–Smith, D.3.5, printed pp. 195–196. This adapter preserves
the original quotient marking and does not assume that the seed is already
irreducible for one component.
-/
@[expose] public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter10
noncomputable local instance movedSeedTypesFieldFourAlgebra :
    Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))

noncomputable abbrev originalSeedCentralImage := quotientImage (ReducedNormal.representation (localJoin T L))
  ((localOrbit T L).subgroupOf (localJoin T L)) D.seedSpace D.homogeneous.invariant

noncomputable def originalSeedProductQuotient :
    (((localOrbit T L).subgroupOf (localJoin T L)) ⧸
      pCore 2 ((localOrbit T L).subgroupOf (localJoin T L))) ≃*
      (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :=
  (QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show localOrbit T L ≤ localJoin T L from le_sup_left))
    (pCore_map_iso 2 _)).trans
    ((QuotientGroup.quotientMulEquivOfEq (originalA5ProductProjection_ker D e hn ht htn).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (originalA5ProductProjection_surjective D e hn ht htn)))

theorem originalSeedProductQuotient_apply (x : (localOrbit T L).subgroupOf (localJoin T L)) :
    originalSeedProductQuotient D e hn ht htn (QuotientGroup.mk' _ x) =
      originalA5ProductProjection D e hn ht htn ⟨x.val.val,x.property⟩ := rfl

noncomputable def originalA5SeedAction : Representation (ZMod 2)
    (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) (originalSeedCentralImage D).toSubmodule := by
  let σ := (originalSeedCentralImage D).toRepresentation
  let : σ.IsIrreducible := quotientImage_irreducible _ D.homogeneous.isIrrPlus
  let τ := quotientOfLEKer σ (pCore 2 _) (normal_p_subgroup_le_ker σ _ pCore_isPGroup)
  exact τ.comp (originalSeedProductQuotient D e hn ht htn).symm.toMonoidHom

theorem originalA5SeedAction_apply (x : (localOrbit T L).subgroupOf (localJoin T L))
    (v : (originalSeedCentralImage D).toSubmodule) :
    originalA5SeedAction D e hn ht htn
      (originalA5ProductProjection D e hn ht htn ⟨x.val.val,x.property⟩) v =
      (originalSeedCentralImage D).toRepresentation x v := by
  let σ := (originalSeedCentralImage D).toRepresentation
  let : σ.IsIrreducible := quotientImage_irreducible _ D.homogeneous.isIrrPlus
  let hk := normal_p_subgroup_le_ker σ (pCore 2 _) pCore_isPGroup
  change quotientOfLEKer σ _ hk ((originalSeedProductQuotient D e hn ht htn).symm
    ((originalSeedProductQuotient D e hn ht htn) (QuotientGroup.mk' _ x))) v = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem originalA5SeedAction_irreducible : (originalA5SeedAction D e hn ht htn).IsIrreducible := by
  let σ := (originalSeedCentralImage D).toRepresentation
  let : σ.IsIrreducible := quotientImage_irreducible _ D.homogeneous.isIrrPlus
  let hk := normal_p_subgroup_le_ker σ (pCore 2 _) pCore_isPGroup
  apply (irreducible_comp_surjective_iff
    (originalSeedProductQuotient D e hn ht htn).symm.toMonoidHom
    (originalSeedProductQuotient D e hn ht htn).symm.surjective _).mpr
  exact (quotientOfLEKer_irreducible_iff σ _ hk).mpr inferInstance

/-- The original seed is already the whole local module if its central
A5-product quotient is the deleted tensor square. -/
theorem source_a5_seed_eq_local_of_deleted_square
    (b : (originalA5SeedAction D e hn ht htn).Equiv
      BinaryPermutation.FiveTensorSquare.deletedAction) :
    D.seed = D.moduleSubgroup := by
  let H := localJoin T L
  let X := (localOrbit T L).subgroupOf H
  let S := (T : Subgroup G).subgroupOf H
  let ρ := ReducedNormal.representation H
  let N := pCore 2 X
  let q := originalSeedProductQuotient D e hn ht htn
  let σ := (originalSeedCentralImage D).toRepresentation
  let δ := BinaryPermutation.FiveTensorSquare.deletedAction
  let b' : σ.Equiv (δ.comp (q.toMonoidHom.comp (QuotientGroup.mk' N))) :=
    Representation.Equiv.mk b.toLinearEquiv (by
      intro x
      apply LinearMap.ext
      intro v
      have he := Representation.IntertwiningMap.isIntertwining
        (originalA5SeedAction D e hn ht htn) δ b.toIntertwiningMap
          (q (QuotientGroup.mk' N x)) v
      rw [originalSeedProductQuotient_apply,originalA5SeedAction_apply] at he
      exact he)
  have hstab : (T : Subgroup G) ≤ normalizer (D.seed : Set G) := by
    intro s hs
    let sH : H := ⟨s,(show (T : Subgroup G) ≤ H from le_sup_right) hs⟩
    let sT : S := ⟨sH,hs⟩
    have he := D.homogeneous.map_eq_of_quotient_model_twist ρ sT N q δ b' (by
      intro a
      obtain ⟨w,hw⟩ := BinaryPermutation.FiveTensorSquare.exists_wreath_intertwiner a
      exact ⟨BinaryPermutation.FiveTensorSquare.tensorWreathHom w,hw⟩)
    have himage := congrArg (ReducedNormal.subspaceImage H) he
    rw [ReducedNormal.subspaceImage_map] at himage
    exact mem_normalizer_iff_map_conj_eq.mpr himage
  exact le_antisymm (le_componentOrbit _ _)
    (iSup_conjugates_le_of_le_normalizer D.seed T D.seed le_rfl hstab)

/-- A proper local seed cannot have the invariant deleted-square type. -/
theorem source_a5_moved_seed_not_deleted_square
    (hproper : D.seed ≠ D.moduleSubgroup) :
    ¬ Nonempty ((originalA5SeedAction D e hn ht htn).Equiv
      BinaryPermutation.FiveTensorSquare.deletedAction) := by
  rintro ⟨b⟩
  exact hproper (source_a5_seed_eq_local_of_deleted_square D e hn ht htn b)

/-- The actual proper seed retains only the natural pair and the two mixed
orientations. Its irreducibility and the deleted-square exclusion are proved
from the original homogeneous setup. -/
theorem source_a5_moved_seed_product_alternatives
    (hproper : D.seed ≠ D.moduleSubgroup)
    (hleft : ∃ g, originalA5SeedAction D e hn ht htn (g,1) ≠ 1)
    (hright : ∃ g, originalA5SeedAction D e hn ht htn (1,g) ≠ 1) :
    Representation.QuadraticFourGroup.TensorClassification.CubicFreeOnFactors
      (originalA5SeedAction D e hn ht htn) ∨
    (∃ f : alternatingGroup (Fin 5) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty ((originalA5SeedAction D e hn ht htn).Equiv
        (Representation.QuadraticFourGroup.TensorClassification.externalTensor
          BinaryPermutation.FiveTensorSquare.δ (Representation.SL2.BinarySmall.natural.comp f.toMonoidHom)))) ∨
    (∃ f : alternatingGroup (Fin 5) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty ((originalA5SeedAction D e hn ht htn).Equiv
        (Representation.QuadraticFourGroup.TensorClassification.externalTensor
          (Representation.SL2.BinarySmall.natural.comp f.toMonoidHom) BinaryPermutation.FiveTensorSquare.δ))) := by
  let := originalA5SeedAction_irreducible D e hn ht htn
  rcases source_a5_product_module_alternatives_without_exchange
      (originalA5SeedAction D e hn ht htn) hleft hright with hf | hd | hn' | hdd
  · exact Or.inl hf
  · exact Or.inr (Or.inl hd)
  · exact Or.inr (Or.inr hn')
  · exact (source_a5_moved_seed_not_deleted_square D e hn ht htn hproper hdd).elim
end CFSG.Quasithin.Chapter10
