module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Data

/-!
# Parity certificate for the exterior annihilator

The parity fold is forced at each step to avoid duplicating unevaluated binary
arithmetic. A kernel check on the list of all 1221 published exterior rows
certifies that the transported functional annihilates each row. Traversing the
list avoids repeated indexed lookups into the large table.

Source and witness conventions: ScalarCertificate/source/README.md.
-/

@[expose] public section
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate

def forcedParity : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => match x with
    | 0 => forcedParity k (0 ^^^ (0 >>> 2 ^ k))
    | y + 1 => forcedParity k ((y + 1) ^^^ ((y + 1) >>> 2 ^ k))

theorem forcedParity_eq (k x : ℕ) : forcedParity k x = foldParity k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => cases x <;> simp only [forcedParity, ih, foldParity]

theorem annihilator_bound : annihilatorBits < 2 ^ 6216 := by decide +kernel

/-- All actual exterior generators have zero parity against the witness. -/
theorem annihilator_list :
    exteriorFormRows.toList.all (fun r =>
      !((forcedParity 13 (annihilatorBits &&& r)).testBit 0)) = true := by
  decide +kernel

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate
