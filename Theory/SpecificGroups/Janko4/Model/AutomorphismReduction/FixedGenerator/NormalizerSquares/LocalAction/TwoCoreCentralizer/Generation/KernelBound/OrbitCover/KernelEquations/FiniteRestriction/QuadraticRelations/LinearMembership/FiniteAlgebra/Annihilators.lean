module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra.Witnesses
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra.Fast

/-! Arithmetic certificates for the mixed-space annihilators and source rows.
See ../source/README.md for the exact finite contract and ATLAS conventions. -/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra
open GeneratorCertificates

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ann_checked : ∀ w : Fin 560, ∀ u : Fin 40,
    (parity600 (annMasks.get w &&& mixedMasks.get u)).testBit 0 = false := by
  decide +kernel

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra
