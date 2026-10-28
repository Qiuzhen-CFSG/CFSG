module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra.Witnesses
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra.Fast
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra.WitnessLookup

/-! Bounded kernel checks for the mixed-space matrix equations.
The row ranges partition the original finite assertions. See ../source/README.md
for the certificate contract and the unchanged ATLAS-coordinate data. -/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra.GeometryChecks
open GeneratorCertificates

private theorem vectors_eq {α : Type*} {n : ℕ} (xs ys : α → Vector ℕ n)
    (h : ∀ i j, (xs i).get j = (ys i).get j) : ∀ i, xs i = ys i := by
  intro i
  apply Vector.ext
  intro j hj
  exact h i ⟨j,hj⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem transpose0100 : ∀ w : Fin 50,
    transRows 50 (annRows ⟨100 + w.val, by omega⟩) = annTransposeRows.get ⟨100 + w.val, by omega⟩ := by
  apply vectors_eq
  simp only [annRows, slices, transRows, annTransposeRows, get_ofFn,
    List.ofFn_succ, List.ofFn_zero]
  simp only [← annMaskLookup_eq, ← transposeMaskLookup_eq]
  intro w
  fin_cases w <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem adjoint0100 : ∀ w : Fin 50,
    mulRows restrictionPairingRows (annTransposeRows.get ⟨100 + w.val, by omega⟩) =
      adjLeftRows.get ⟨100 + w.val, by omega⟩ := by
  apply vectors_eq
  simp only [mulRows, annTransposeRows, slices, get_ofFn, Vector.toList_ofFn,
    List.ofFn_succ, List.ofFn_zero]
  simp only [← transposeMaskLookup_eq, ← adjLeftLookup_eq]
  intro w
  fin_cases w <;> decide +kernel

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra.GeometryChecks
