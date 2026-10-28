module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedKernel.CrossData
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorInvariance

/-!
# Linear constraints on the full seed action kernel

A kernel actor fixes every seed-fixed column. For an ambient invariant form R,
its pullback minus R therefore vanishes on pairs of fixed columns. Its mixed
restriction is linear in the actor displacement D, namely Wᵀ R D U.

This gives necessary linear conditions on D once the finite restriction bound
for the exterior space has been certified. Ambient preservation follows from
the two original generators; no containment in a local word subgroup is used.
See `FixedKernel/source/README.md` for the remaining finite certificates and
GLS3 Table 5.3i for the centralizer motivation.
-/

set_option maxRecDepth 2048

@[expose] public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder.SeedKernel

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
  (exteriorFormSpace exteriorBasisForm_mem formPullback formStabilizer
    matrixGroup_le_formStabilizer matrixUnitA_mem_exteriorFormStabilizer
    matrixUnitB_mem_exteriorFormStabilizer)

attribute [local irreducible] modelGroup matrixA matrixB fixedAction naturalAction
  Cardinality.localKernelSeed Cardinality.max1Subgroup
  seedMatrixDisplacement seedFixedColumns crossRestriction fixedRestriction
  candidateCrossSpace testForm exteriorFormSpace

/-- The matrix displacement agrees with the published natural linear action. -/
theorem seedMatrixDisplacement_mulVec (v : NaturalModule) :
    seedMatrixDisplacement.mulVec v = displacement v := by
  rw [seedMatrixDisplacement, Matrix.sub_mulVec, Matrix.one_mulVec,
    displacement_apply]

/-- Two fixed-action kernel displacements multiply to zero in matrix coordinates. -/
theorem kernel_matrix_displacement_mul (c d : fixedAction.ker) :
    (toMatrix (c.val : Model) - 1) * (toMatrix (d.val : Model) - 1) = 0 := by
  apply Matrix.mulVec_injective
  funext v
  have h := LinearMap.congr_fun (kernel_displacement_mul c d) v
  change naturalAction c.val (naturalAction d.val v - v) -
    (naturalAction d.val v - v) = 0 at h
  simp only [naturalAction_apply] at h
  simpa only [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.zero_mulVec] using h

/-- The seed annihilates every kernel displacement on both sides. -/
theorem kernel_matrix_annihilation (c : fixedAction.ker) :
    seedMatrixDisplacement * (toMatrix (c.val : Model) - 1) = 0 ∧
      (toMatrix (c.val : Model) - 1) * seedMatrixDisplacement = 0 := by
  let s : fixedAction.ker := ⟨markedSeed, markedSeed_mem_fixedAction_ker⟩
  unfold seedMatrixDisplacement
  exact ⟨kernel_matrix_displacement_mul s c, kernel_matrix_displacement_mul c s⟩

/-- Every kernel actor fixes the chosen seed-fixed columns. -/
theorem kernel_fixes_columns (c : fixedAction.ker) :
    toMatrix (c.val : Model) * seedFixedColumns = seedFixedColumns := by
  have h := (kernel_matrix_annihilation c).2
  have h' : (toMatrix (c.val : Model) - 1) * seedFixedColumns = 0 := by
    rw [seedFixedColumns, ← Matrix.mul_assoc, h, Matrix.zero_mul]
  simpa only [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] using h'

/-- Every member of the original ambient model preserves the published
exterior-form space, using its generator certificates. -/
theorem model_preserves_exteriorSpace (g : Model) :
    toAmbient g ∈ formStabilizer exteriorFormSpace :=
  matrixGroup_le_formStabilizer exteriorFormSpace
    matrixUnitA_mem_exteriorFormStabilizer matrixUnitB_mem_exteriorFormStabilizer
    (show toAmbient g ∈ matrixGroup from g.property)

private theorem kernel_transpose_fixes_columns (c : fixedAction.ker) :
    seedFixedColumns.transpose * (toMatrix (c.val : Model)).transpose =
      seedFixedColumns.transpose := by
  simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose (kernel_fixes_columns c)

/-- A kernel pullback difference vanishes on pairs of fixed columns. -/
theorem kernel_pullback_fixedRestriction (c : fixedAction.ker) (R : BinaryMatrix) :
    fixedRestriction (formPullback (toAmbient (c.val : Model)) R - R) = 0 := by
  have hleft := kernel_transpose_fixes_columns c
  have hright := kernel_fixes_columns c
  unfold fixedRestriction formPullback
  change seedFixedColumns.transpose *
    ((toMatrix (c.val : Model)).transpose * R * toMatrix (c.val : Model) - R) *
      seedFixedColumns = 0
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [← Matrix.mul_assoc, hleft]
  rw [Matrix.mul_assoc _ (toMatrix (c.val : Model)), hright, sub_self]

/-- The mixed restriction of a kernel pullback difference is linear in its
displacement. No quadratic term remains because the first column is fixed. -/
theorem kernel_pullback_crossRestriction (c : fixedAction.ker) (R : BinaryMatrix) :
    crossRestriction (formPullback (toAmbient (c.val : Model)) R - R) =
      crossRestriction (R * (toMatrix (c.val : Model) - 1)) := by
  have hleft := kernel_transpose_fixes_columns c
  unfold crossRestriction formPullback
  change seedFixedColumns.transpose *
    ((toMatrix (c.val : Model)).transpose * R * toMatrix (c.val : Model) - R) *
      complementColumns =
    seedFixedColumns.transpose * (R * (toMatrix (c.val : Model) - 1)) * complementColumns
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, ← Matrix.mul_assoc, hleft]

/-- Reduce every full ambient kernel actor to the same finite linear system.
The premise is only the exterior-space restriction certificate, independent of
ambient membership and of the separate linear-system rigidity certificate. -/
theorem kernel_linearConditions
    (hrestriction : ∀ R ∈ exteriorFormSpace, fixedRestriction R = 0 →
      crossRestriction R ∈ candidateCrossSpace)
    (c : fixedAction.ker) : LinearConditions (toMatrix (c.val : Model) - 1) := by
  refine ⟨(kernel_matrix_annihilation c).1, (kernel_matrix_annihilation c).2, ?_⟩
  intro i
  have hR : testForm i ∈ exteriorFormSpace := by
    unfold testForm
    exact exteriorBasisForm_mem _
  have hp : formPullback (toAmbient (c.val : Model)) (testForm i) ∈ exteriorFormSpace :=
    ((model_preserves_exteriorSpace (c.val : Model)) _).mpr hR
  have h := hrestriction _ (exteriorFormSpace.sub_mem hp hR)
    (kernel_pullback_fixedRestriction c (testForm i))
  rwa [kernel_pullback_crossRestriction] at h

end Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder.SeedKernel
