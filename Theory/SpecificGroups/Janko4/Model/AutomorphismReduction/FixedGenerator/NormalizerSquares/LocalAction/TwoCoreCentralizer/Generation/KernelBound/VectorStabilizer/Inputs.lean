module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorAction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorInvariance
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership

/-!
# Inputs for the marked stabilizer calculation

Fixation of the actual marked vector supplies the chart-reconstruction input
to the proved 125-space theorem; general affine reconstruction is unnecessary.
The displacement restriction fixes the first coordinate vector and preserves
the entire restricted exterior span. Actual homology-kernel elements supply
both invariant-form premises through the literal generated matrix group.
The final transfer retains the finite matrix implication as an explicit input.

Source conventions and the remaining finite argument are in source/README.md.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership

attribute [local irreducible] restrictionEmbedding restrictionExtraction restrictionMatrix

theorem fixed_base_reconstruction (g : BinaryMatrixˣ)
    (hfix : (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) = baseVector) :
    (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) =
      synthesize (coordinates ((g : BinaryMatrix) *ᵥ (baseVector : NaturalModule))) := by
  rw [hfix]
  simpa only [quadraticVector_zero] using (quadraticVector_satisfies 0).1

theorem restriction_mem_of_fixed_base (g : BinaryMatrixˣ)
    (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (hfix : (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) = baseVector) :
    restrictionMatrix g ∈ restrictionLinearSpace :=
  restrictionMatrix_mem_linearSpace g hker hform hext (fixed_base_reconstruction g hfix)

theorem restriction_fixes_first (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hfix : (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) = baseVector) :
    restrictionMatrix g *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  have h := restrictionImage_matrix g hker
  rw [hfix, ← restrictionEmbedding_zero] at h
  change restrictionEmbedding *ᵥ (restrictionMatrix g *ᵥ Pi.single 0 1) =
    restrictionEmbedding *ᵥ Pi.single 0 1 at h
  have he := congrArg (fun v => restrictionExtraction *ᵥ v) h
  simpa only [Matrix.mulVec_mulVec _ restrictionExtraction restrictionEmbedding,
    restrictionExtraction_embedding, Matrix.one_mulVec] using he

/-- Preservation holds for every member of the actual restricted exterior span. -/
theorem restriction_preserves_exterior (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hext : g ∈ formStabilizer exteriorFormSpace) {R : RestrictionMatrix}
    (hR : R ∈ restrictionExteriorSpace) :
    (restrictionMatrix g)ᵀ * R * restrictionMatrix g ∈ restrictionExteriorSpace := by
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨i, rfl⟩ := hR
    rw [restrictionForm_pullback_of_intertwining g _ (restrictionMatrix_intertwining g hker)]
    exact restrictionForm_mem ((hext _).mpr (exteriorBasisForm_mem i))
  | zero => simp
  | add R T _ _ hR hT =>
    simpa only [Matrix.mul_add, Matrix.add_mul] using restrictionExteriorSpace.add_mem hR hT
  | smul r R _ hR =>
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using restrictionExteriorSpace.smul_mem r hR

/-- All structural inputs come from membership in the literal matrix group. -/
theorem actual_kernel_inputs (c : homologyAction.ker) :
    KernelConditions ((c : involutionCentralizer) : BinaryMatrixˣ) ∧
      formPullback ((c : involutionCentralizer) : BinaryMatrixˣ) invariantForm = invariantForm ∧
      ((c : involutionCentralizer) : BinaryMatrixˣ) ∈ formStabilizer exteriorFormSpace := by
  have hc : ((c : involutionCentralizer) : BinaryMatrixˣ) ∈ matrixGroup :=
    involutionCentralizer_le_matrixGroup (c : involutionCentralizer).property
  exact ⟨kernel_conditions c, matrixGroup_preserves_invariantForm hc,
    matrixGroup_le_formStabilizer exteriorFormSpace
      matrixUnitA_mem_exteriorFormStabilizer matrixUnitB_mem_exteriorFormStabilizer hc⟩

/-- Transfer the finite matrix implication to the exact public group statement.
The finite implication remains an explicit prerequisite here. -/
theorem vector_stabilizer_of_finite_implication
    (hfinite : ∀ g : BinaryMatrixˣ, KernelConditions g →
      formPullback g invariantForm = invariantForm →
      g ∈ formStabilizer exteriorFormSpace →
      (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) = baseVector →
      g = 1 ∨ g = matrixUnitA)
    (c : homologyAction.ker)
    (hc : naturalAction (c : involutionCentralizer) (baseVector : NaturalModule) = baseVector) :
    (c : involutionCentralizer) = 1 ∨ (c : involutionCentralizer) = centralInvolution := by
  obtain ⟨hk, hf, he⟩ := actual_kernel_inputs c
  have hx := hfinite ((c : involutionCentralizer) : BinaryMatrixˣ) hk hf he
    (by simpa only [naturalAction_apply] using hc)
  exact hx.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
