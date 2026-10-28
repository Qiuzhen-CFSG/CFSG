module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.CompletenessData
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.CoefficientKernel.Checked

/-!
# The coefficient kernel of the selected evaluation table

Every coefficient vector killed by the published 1168-by-1221 binary table
is reconstructed from its 53 displayed free coordinates using the published
radical coefficient columns. The proof checks D T = 1 + K F row by row and
applies it to the vector. It does not assume any interpretation of the table
as form evaluations.

This is the independent coefficient-kernel contract in source/README.md.
The witnesses come from source/generate_completeness.py; their assertions are
replaced by kernel-checked identities in CoefficientKernel/Checked.lean.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate

/-- The published radical coefficient columns reconstruct the entire kernel. -/
theorem coefficient_kernel (c : Fin 1221 → ZMod 2)
    (hc : coefficientEvaluationMatrix *ᵥ c = 0) :
    c = radicalCoefficientMatrix *ᵥ freeCoefficients c :=
  CoefficientKernel.kernel_of_checks CoefficientKernel.allRowChecks c hc

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate
