module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Data

/-! The row-major upper triangle of a 112 by 112 matrix has 6216 positions.
The finite checks prove that the displayed square-root indexing enumerates each
position exactly once. Source conventions: ScalarCertificate/source/README.md. -/

@[expose] public section
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate.ExteriorIndex

private instance finForall {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∀ i, P i) := Nat.decidableForallFin P

theorem all_factors {a b : ℕ} {P : Fin (a * b) → Prop}
    (h : ∀ i : Fin a, ∀ j : Fin b, P (finProdFinEquiv (i, j))) : ∀ k, P k := by
  intro k
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  exact h i j

def upperPair (k : Fin 6216) : Fin 112 × Fin 112 :=
  (⟨(upperPairs.get k / 112) % 112, Nat.mod_lt _ (by decide)⟩,
   ⟨upperPairs.get k % 112, Nat.mod_lt _ (by decide)⟩)

def upperIndex (p : Fin 112 × Fin 112) : Fin 6216 :=
  ⟨exteriorIndex p.1 p.2 % 6216, Nat.mod_lt _ (by decide)⟩

theorem upperPair_lt : ∀ k : Fin 6216, (upperPair k).1 < (upperPair k).2 := by
  refine all_factors (a := 56) (b := 111) ?_
  simp only [upperPair, upperPairs, get_ofFn]
  decide +kernel

theorem upperPair_index : ∀ k : Fin 6216,
    exteriorIndex (upperPair k).1 (upperPair k).2 = k.val := by
  refine all_factors (a := 56) (b := 111) ?_
  simp only [upperPair, upperPairs, get_ofFn]
  decide +kernel

theorem upperPair_inverse : ∀ i j : Fin 112, i < j →
    upperPair (upperIndex (i,j)) = (i,j) := by
  simp only [upperPair, upperIndex, upperPairs, get_ofFn]
  decide +kernel


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate.ExteriorIndex
