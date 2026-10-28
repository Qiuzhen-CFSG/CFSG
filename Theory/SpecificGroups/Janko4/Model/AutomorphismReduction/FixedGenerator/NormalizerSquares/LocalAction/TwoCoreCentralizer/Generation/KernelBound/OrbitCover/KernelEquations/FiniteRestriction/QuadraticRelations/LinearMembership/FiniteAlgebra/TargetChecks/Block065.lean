module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra.Witnesses

/-! Bounded checks relating the reconstructed vectors to the unchanged target
span. See ../source/README.md for provenance and the complete finite contract. -/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra.TargetChecks
open GeneratorCertificates

private theorem vectors_eq {α : Type*} {n : ℕ} (xs ys : α → Vector ℕ n)
    (h : ∀ i j, (xs i).get j = (ys i).get j) : ∀ i, xs i = ys i := by
  intro i
  apply Vector.ext
  intro j hj
  exact h i ⟨j,hj⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem basis065 : ∀ i : Fin 5,
    slices 50 50 (targetMasks.get ⟨65 + i.val, by omega⟩) = restrictionLinearRows.get ⟨65 + i.val, by omega⟩ := by
  apply vectors_eq
  simp only [slices, get_ofFn]
  intro i
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem kernel065 : ∀ i : Fin 5,
    scan (kernelCoefficients.get ⟨65 + i.val, by omega⟩) targetMasks.toList = kernelMasks.get ⟨65 + i.val, by omega⟩ := by
  intro i
  fin_cases i <;> decide +kernel

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra.TargetChecks
