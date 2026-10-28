module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.Coordinates
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorSpace
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.InvariantForm
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorInvariance
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction

/-!
# An ambient exterior-square route to the kernel equations

The literal matrix group preserves an explicitly certified bilinear form
and the span of 1221 explicit alternating forms. Preservation by the two
ambient generators extends to the entire generated matrix group.
The finite restriction theorem deduces reconstruction, normalization, and
all nine quadratic column equations from these invariants and the exact
homology-kernel condition.

The final theorem applies this argument to every element of the full
centralizer's homology kernel, discharging all certificate premises without
local generation or word evaluation. GLS3 Table 5.3i, printed p.270, motivates
the target but does not identify this natural homology kernel.
See KernelEquations/source/README.md for the ambient invariant route.
-/

@[expose] public section
open scoped Matrix

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

/-- Assembly from ambient generator certificates and a finite matrix theorem.
The unconditional theorem below supplies all three certificates. -/
theorem kernel_image_satisfies_equations_of_exterior_certificates
    (hA : matrixUnitA ∈ formStabilizer exteriorFormSpace)
    (hB : matrixUnitB ∈ formStabilizer exteriorFormSpace)
    (hrestriction : ∀ g : BinaryMatrixˣ,
      KernelConditions g →
      formPullback g invariantForm = invariantForm →
      g ∈ formStabilizer exteriorFormSpace →
      SatisfiesEquations ((g : BinaryMatrix) *ᵥ (baseVector : NaturalModule)))
    (c : homologyAction.ker) :
    SatisfiesEquations (naturalAction (c : involutionCentralizer)
      (baseVector : NaturalModule)) := by
  have hg : ((c : involutionCentralizer) : BinaryMatrixˣ) ∈ matrixGroup :=
    involutionCentralizer_le_matrixGroup (c : involutionCentralizer).property
  rw [naturalAction_apply]
  exact hrestriction _ (kernel_conditions c)
    (matrixGroup_preserves_invariantForm hg)
    (matrixGroup_le_formStabilizer exteriorFormSpace hA hB hg)

/-- Every element of the full centralizer's natural-homology kernel sends the
base vector to a column satisfying the explicit reconstruction, normalization,
and nine quadratic equations. -/
theorem kernel_image_satisfies_equations (c : homologyAction.ker) :
    SatisfiesEquations (naturalAction (c : involutionCentralizer)
      (baseVector : NaturalModule)) :=
  kernel_image_satisfies_equations_of_exterior_certificates
    matrixUnitA_mem_exteriorFormStabilizer matrixUnitB_mem_exteriorFormStabilizer
    matrix_equations_of_exterior_stabilizer c

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
