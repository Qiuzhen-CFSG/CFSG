module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra.Soundness
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra.Trace

/-!
# The finite mixed-space implication

The two preservation hypotheses and reconstruction give 2375 explicit binary
linear equations on the 2500 entries. A kernel-checked XOR elimination trace
reconstructs every solution from 125 free entries. Each reconstructed vector
is a checked linear combination of the unchanged restrictionLinearBasis.

This is the independent finite linear-algebra implication specified in
source/README.md. No group-theoretic or quadratic hypothesis is used.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership
open FiniteAlgebra

/-- Mixed-space preservation on both sides of the pairing adjoint, together
with reconstruction of the base-column image, forces the prescribed span. -/
theorem mem_restrictionLinearSpace_of_mixed (S : RestrictionMatrix)
    (hS : PreservesMixedSpace S)
    (hA : PreservesMixedSpace (pairingAdjoint S))
    (h : restrictionImage S = synthesize (coordinates (restrictionImage S))) :
    S ∈ restrictionLinearSpace := by
  have hx := kernel_reconstruct (flat S) (raw_vanish S hS hA h)
  have heq := congrArg (unflat (m := 50) (n := 50)) hx
  rw [unflat_flat, unflat_sum] at heq
  rw [heq]
  apply Submodule.sum_mem
  intro k _
  rw [unflat_smul]
  exact Submodule.smul_mem _ _ (kernel_mem k)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership
