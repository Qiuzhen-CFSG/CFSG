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

private theorem get_ite {α : Type*} {n : ℕ} (b : Prop) [Decidable b]
    (xs ys : Vector α n) (j : Fin n) :
    (if b then xs else ys).get j = if b then xs.get j else ys.get j := by
  split <;> rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem source1850 : ∀ k : Fin 50,
    sourceRows ⟨1850 + k.val, by omega⟩ = slices 50 50 (rawMasks.get ⟨1850 + k.val, by omega⟩) := by
  apply vectors_eq
  simp only [sourceRows, annRows, slices, mulRows, transRows, get_ite, get_ofFn,
    Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero]
  simp only [← choiceLookup_eq, ← adjLeftLookup_eq, ← annMaskLookup_eq, ← rawMaskLookup_eq]
  intro k
  fin_cases k <;> decide +kernel

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra.GeometryChecks
