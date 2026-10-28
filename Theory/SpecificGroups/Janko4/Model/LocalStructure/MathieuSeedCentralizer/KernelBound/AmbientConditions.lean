module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.FormConstraints
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorInvariance

/-!
# Actual ambient centralizer and local-kernel interfaces

The order-2048 normal closure in max1 embeds in the full seed centralizer
because its independently certified generators commute. The restriction map
uses the literal adapted coordinates. Both form invariants hold for every
ambient model element, hence for every full-centralizer element.

Source: the ATLAS words documented in `Cardinality.Subgroup`, the existing
kernel-count certificates, and the generator-certified exterior space. This
module does not identify the full centralizer with any local subgroup.
-/

@[expose] public section

open scoped Matrix

namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound
open Cardinality Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

abbrev SeedCentralizer := ambientSeedCentralizer matrixA_mul_self matrixB_pow_four

def ambientKernel : Subgroup Model :=
  (localKernel matrixA_mul_self matrixB_pow_four).map
    (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernelSeed

theorem ambientKernel_card : Nat.card ambientKernel = 2048 := by
  rw [ambientKernel, Subgroup.card_map_of_injective
    (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype_injective, localKernel_card]

theorem seed_mem_ambientKernel :
    (localKernelSeed matrixA_mul_self matrixB_pow_four : Model) ∈ ambientKernel :=
  ⟨_, localKernelSeed_mem _ _, rfl⟩

theorem ambientKernel_le_centralizer : ambientKernel ≤ SeedCentralizer := by
  rintro g ⟨z, hz, rfl⟩ t ht
  obtain rfl := Set.mem_singleton_iff.mp ht
  exact congrArg (fun w : max1Subgroup matrixA_mul_self matrixB_pow_four => (w : Model))
    (QuotientCount.Image.localKernel_commute _ _ _ (localKernelSeed_mem _ _) z hz)

def kernelCentralizerInclusion : ambientKernel →* SeedCentralizer :=
  Subgroup.inclusion ambientKernel_le_centralizer

theorem seed_matrix :
    toMatrix (localKernelSeed matrixA_mul_self matrixB_pow_four : Model) =
      decodeRows Cardinality.KernelCount.e0Rows :=
  Cardinality.KernelCount.Relations.representation_seed _ _

theorem centralizer_matrix_commutes (c : SeedCentralizer) :
    toMatrix (c : Model) * decodeRows Cardinality.KernelCount.e0Rows =
      decodeRows Cardinality.KernelCount.e0Rows * toMatrix (c : Model) := by
  have h := c.property _ (Set.mem_singleton _)
  have he := congrArg toMatrix h
  simpa only [map_mul, seed_matrix] using he.symm

def restriction : SeedCentralizer →* HalfMatrix where
  toFun c := restrictionBlock (toMatrix (c : Model))
  map_one' := by simp only [OneMemClass.coe_one, map_one, restrictionBlock_one]
  map_mul' c d := by
    simp only [Subgroup.coe_mul, map_mul]
    exact restrictionBlock_mul _ _ (centralizer_matrix_commutes c) (centralizer_matrix_commutes d)

theorem centralizer_block_shape (c : SeedCentralizer) :
    blockCoordinates (toMatrix (c : Model)) =
      Matrix.fromBlocks (restriction c) (shearBlock (toMatrix (c : Model))) 0 (restriction c) :=
  centralizing_block_shape _ (centralizer_matrix_commutes c)

theorem model_preserves_exterior (g : Model) :
    toAmbient g ∈ formStabilizer exteriorFormSpace :=
  matrixGroup_le_formStabilizer exteriorFormSpace matrixUnitA_mem_exteriorFormStabilizer
    matrixUnitB_mem_exteriorFormStabilizer g.property

theorem centralizer_preserves_exterior (c : SeedCentralizer) :
    toAmbient (c : Model) ∈ formStabilizer exteriorFormSpace :=
  model_preserves_exterior c

theorem centralizer_preserves_pairing (c : SeedCentralizer) :
    formPullback (toAmbient (c : Model)) invariantForm = invariantForm :=
  matrixGroup_preserves_invariantForm (c : Model).property

/-- Every model element preserves the transported exterior space. -/
theorem model_preserves_adaptedExterior (g : Model) :
    ∀ F ∈ adaptedExteriorSpace, (blockCoordinates (toMatrix g))ᵀ * F *
      blockCoordinates (toMatrix g) ∈ adaptedExteriorSpace := by
  rintro F ⟨R, hR, rfl⟩
  refine ⟨formPullback (toAmbient g) R, (model_preserves_exterior g R).mpr hR, ?_⟩
  exact formCoordinates_pullback (toMatrix g) R

/-- The ambient bilinear invariant in the same coordinates as the exterior space. -/
theorem centralizer_preserves_adaptedPairing (c : SeedCentralizer) :
    (blockCoordinates (toMatrix (c : Model)))ᵀ * formCoordinates invariantForm *
      blockCoordinates (toMatrix (c : Model)) = formCoordinates invariantForm := by
  have h := congrArg formCoordinates (centralizer_preserves_pairing c)
  change formCoordinates ((toMatrix (c : Model))ᵀ * invariantForm * toMatrix (c : Model)) = _ at h
  rwa [formCoordinates_pullback] at h

/-- A centralizer element fixing K pointwise satisfies every mixed-block test. -/
theorem centralizer_shear_mixed_constraint (c : SeedCentralizer) (hc : restriction c = 1)
    (F : BlockMatrix) (hF : F ∈ adaptedExteriorSpace) :
    F.toBlocks₁₁ * shearBlock (toMatrix (c : Model)) ∈ mixedKernelSpace := by
  have hs : blockCoordinates (toMatrix (c : Model)) =
      shearMatrix (shearBlock (toMatrix (c : Model))) := by
    rw [centralizer_block_shape, hc]
    rfl
  apply shear_mixed_constraint _ ?_ F hF
  simpa only [hs] using model_preserves_adaptedExterior (c : Model)

/-- The Wall-pairing constraint for a pointwise-fixed shear in the full centralizer. -/
theorem centralizer_shear_pairing_constraint (c : SeedCentralizer) (hc : restriction c = 1) :
    (wallPairing * shearBlock (toMatrix (c : Model)))ᵀ =
      wallPairing * shearBlock (toMatrix (c : Model)) := by
  have hs : blockCoordinates (toMatrix (c : Model)) =
      shearMatrix (shearBlock (toMatrix (c : Model))) := by
    rw [centralizer_block_shape, hc]
    rfl
  apply shear_pairing_constraint
  simpa only [hs] using centralizer_preserves_adaptedPairing c

/-- Restriction-space preservation, valid for the whole centralizer. -/
theorem centralizer_preserves_restrictionSpace (c : SeedCentralizer) :
    ∀ R ∈ restrictionSpace, (restriction c)ᵀ * R * restriction c ∈ restrictionSpace := by
  rintro R ⟨F, hF, rfl⟩
  refine ⟨(blockCoordinates (toMatrix (c : Model)))ᵀ * F *
    blockCoordinates (toMatrix (c : Model)), model_preserves_adaptedExterior c F hF, ?_⟩
  rw [centralizer_block_shape, triangular_pullback_upper]

/-- Once the shear is zero or identity, faithfulness identifies the actual group element. -/
theorem centralizer_eq_one_or_seed_of_shear (c : SeedCentralizer) (hc : restriction c = 1)
    (hH : shearBlock (toMatrix (c : Model)) = 0 ∨ shearBlock (toMatrix (c : Model)) = 1) :
    (c : Model) = 1 ∨ (c : Model) = (localKernelSeed matrixA_mul_self matrixB_pow_four : Model) := by
  rcases hH with h | h
  · left
    apply toMatrix_injective
    apply blockCoordinates_injective
    rw [map_one, blockCoordinates_one, centralizer_block_shape, hc, h, Matrix.fromBlocks_one]
  · right
    apply toMatrix_injective
    apply blockCoordinates_injective
    rw [centralizer_block_shape, hc, h, seed_matrix, blockCoordinates_seed]

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound
