module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.RestrictionData

/-!
# Transport of the exterior conditions to displacement coordinates

An intertwining identity `g E = E S` transports ambient pullback to the
restricted forms and identifies the zeroth column with the ambient base image.
The proofs are rectangular matrix identities and linear-span induction. They
do not assert the intertwining identity for the proposed coordinate extractor;
that finite displacement-coordinate certificate is a separate obligation.

Here `E` is `restrictionEmbedding`. The original exterior forms and column
conventions are those in `KernelEquations/source/README.md`.
-/

@[expose] public section
open scoped Matrix

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

theorem restrictionForm_mem {R : BinaryMatrix} (hR : R ∈ exteriorFormSpace) :
    restrictionForm R ∈ restrictionExteriorSpace := by
  change R ∈ Submodule.span (ZMod 2) (Set.range exteriorBasisForm) at hR
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨i, rfl⟩ := hR
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp [restrictionForm]
  | add R T _ _ hR hT =>
    simpa only [restrictionForm, Matrix.mul_add, Matrix.add_mul] using
      restrictionExteriorSpace.add_mem hR hT
  | smul r R _ hR =>
    simpa only [restrictionForm, Matrix.mul_smul, Matrix.smul_mul] using
      restrictionExteriorSpace.smul_mem r hR

theorem restrictionForm_pullback_of_intertwining (g : BinaryMatrixˣ)
    (S : RestrictionMatrix)
    (hint : (g : BinaryMatrix) * restrictionEmbedding = restrictionEmbedding * S)
    (R : BinaryMatrix) :
    Sᵀ * restrictionForm R * S = restrictionForm (formPullback g R) := by
  calc
    _ = (restrictionEmbedding * S)ᵀ * R * (restrictionEmbedding * S) := by
      simp only [restrictionForm, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = ((g : BinaryMatrix) * restrictionEmbedding)ᵀ * R *
        ((g : BinaryMatrix) * restrictionEmbedding) := by rw [hint]
    _ = _ := by
      simp only [restrictionForm, formPullback, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Only forward preservation is needed for the finite polynomial test. -/
theorem restrictionTestForm_preserved_of_intertwining (g : BinaryMatrixˣ)
    (S : RestrictionMatrix)
    (hint : (g : BinaryMatrix) * restrictionEmbedding = restrictionEmbedding * S)
    (hext : g ∈ formStabilizer exteriorFormSpace) (i : Fin 9) :
    Sᵀ * restrictionTestForm i * S ∈ restrictionExteriorSpace := by
  rw [restrictionTestForm, restrictionForm_pullback_of_intertwining g S hint]
  exact restrictionForm_mem ((hext _).mpr (exteriorBasisForm_mem _))

theorem restrictionImage_eq_of_intertwining (g : BinaryMatrixˣ)
    (S : RestrictionMatrix)
    (hint : (g : BinaryMatrix) * restrictionEmbedding = restrictionEmbedding * S) :
    restrictionImage S = (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) := by
  rw [restrictionImage, Matrix.mulVec_mulVec, ← hint, ← Matrix.mulVec_mulVec,
    restrictionEmbedding_zero]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
