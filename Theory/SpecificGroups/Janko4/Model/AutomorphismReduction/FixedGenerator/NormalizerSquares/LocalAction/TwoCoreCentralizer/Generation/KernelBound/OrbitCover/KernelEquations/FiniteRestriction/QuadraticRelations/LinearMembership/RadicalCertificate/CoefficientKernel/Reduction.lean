module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.CompletenessData

/-!
# Reconstruction from packed coefficient row certificates

The two checks in each row identify D T with the published remainder and
identify that remainder with 1 + K F. Here F selects the displayed free
positions and K has the radical coefficient vectors as columns. Applying the
identity to a vector killed by T gives c = K (F c), in characteristic two.

The numerical witnesses and their generation are described in
../source/README.md and ../source/generate_completeness.py. This module only
proves the algebraic transfer; Checked.lean discharges every row check.
-/

public section

open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate
open GeneratorCertificates
namespace CoefficientKernel

/-- Packed row of the proposed matrix 1 + K F. -/
@[expose] def remainderWord (i : Fin 1221) : ℕ :=
  2 ^ i.val ^^^ xorList (List.ofFn (fun k : Fin 53 =>
    if (radicalCoefficients.get k).testBit i.val
    then 2 ^ (freeCoefficientIndices.get k).val else 0))

/-- Both numerical identities needed for one coefficient row. -/
@[expose] def RowChecks (i : Fin 1221) : Prop :=
  scan (coefficientRecoveryRows.get i) coefficientEvaluationRows.toList =
    coefficientRemainderRows.get i ∧
  coefficientRemainderRows.get i = remainderWord i

private def selectionMatrix : Matrix (Fin 53) (Fin 1221) (ZMod 2) :=
  fun k j => if freeCoefficientIndices.get k = j then 1 else 0

private theorem selection_mulVec (c : Fin 1221 → ZMod 2) :
    selectionMatrix *ᵥ c = freeCoefficients c := by
  ext k
  simp [Matrix.mulVec, dotProduct, selectionMatrix, freeCoefficients]

set_option maxRecDepth 10000 in
private theorem remainder_decode (h : ∀ i, coefficientRemainderRows.get i = remainderWord i) :
    rectDecode 1221 coefficientRemainderRows = 1 + radicalCoefficientMatrix * selectionMatrix := by
  ext i j
  simp only [rectDecode, h, remainderWord, bit_xor, bit_xorList,
    List.map_ofFn, List.sum_ofFn, Matrix.add_apply, Matrix.mul_apply]
  apply congrArg₂ (· + ·)
  · simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
  · apply Finset.sum_congr rfl
    intro k _
    simp only [radicalCoefficientMatrix, Matrix.transpose_apply, rectDecode, selectionMatrix]
    cases hb : (radicalCoefficients.get k).testBit i.val <;>
      simp [hb, bit, Nat.testBit_two_pow, Fin.ext_iff]

set_option maxRecDepth 10000 in
/-- Row certificates imply reconstruction of every vector in the kernel. -/
theorem kernel_of_checks (h : ∀ i, RowChecks i) (c : Fin 1221 → ZMod 2)
    (hc : coefficientEvaluationMatrix *ᵥ c = 0) :
    c = radicalCoefficientMatrix *ᵥ freeCoefficients c := by
  have hd : rectDecode 1168 coefficientRecoveryRows * coefficientEvaluationMatrix =
      rectDecode 1221 coefficientRemainderRows := by
    apply rectProduct_eq
    intro i
    rw [← scan_eq]
    exact (h i).1
  have hz := congrArg (fun M => M *ᵥ c) hd
  rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero,
    remainder_decode (fun i => (h i).2), Matrix.add_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, selection_mulVec] at hz
  ext i
  have hi := congrFun hz i
  change 0 = c i + (radicalCoefficientMatrix *ᵥ freeCoefficients c) i at hi
  exact (eq_neg_of_add_eq_zero_left hi.symm).trans (CharTwo.neg_eq _)

end CoefficientKernel
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate

