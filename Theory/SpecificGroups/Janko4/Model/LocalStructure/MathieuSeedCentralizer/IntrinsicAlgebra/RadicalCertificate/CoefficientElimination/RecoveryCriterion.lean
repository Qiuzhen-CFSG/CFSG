module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.CoefficientElimination.EvaluationCriterion

/-!
# Coefficient reconstruction from a checked recovery matrix

The identity D T = 1 + K F reconstructs any coefficient vector killed by T
from its ten prescribed free entries. K consists of the exact literal radical
coefficient words; F selects `radicalCoordinateIndex`. All row identities
remain explicit here and are discharged in `Recovery`. See source/README.md.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
namespace CoefficientElimination

def remainderWord (i : Fin 1221) : ℕ :=
  2 ^ i.val ^^^ GeneratorCertificates.xorList (List.ofFn (fun k : Fin 10 =>
    if (radicalCoefficients.get k).testBit i.val
    then 2 ^ (radicalCoordinateIndex k).val else 0))

def RowChecks (i : Fin 1221) : Prop :=
  scan (recoveryRows.get i) evaluationRows.toList = remainderRows.get i ∧
  remainderRows.get i = remainderWord i

private def selectionMatrix : Matrix (Fin 10) (Fin 1221) (ZMod 2) :=
  fun k j => if radicalCoordinateIndex k = j then 1 else 0

private def radicalMatrix : Matrix (Fin 1221) (Fin 10) (ZMod 2) :=
  fun j k => bit (radicalCoefficients.get k) j.val

private theorem selection_mulVec (c : Fin 1221 → ZMod 2) :
    selectionMatrix *ᵥ c = fun k => c (radicalCoordinateIndex k) := by
  ext k
  simp [Matrix.mulVec, dotProduct, selectionMatrix]

set_option maxRecDepth 10000 in
private theorem remainder_decode (h : ∀ i, remainderRows.get i = remainderWord i) :
    rows 1221 remainderRows = 1 + radicalMatrix * selectionMatrix := by
  ext i j
  change GeneratorCertificates.bit _ _ = _
  simp only [h, remainderWord, GeneratorCertificates.bit_xor,
    GeneratorCertificates.bit_xorList, List.map_ofFn, List.sum_ofFn,
    Matrix.add_apply, Matrix.mul_apply]
  apply congrArg₂ (· + ·)
  · simp [GeneratorCertificates.bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
  · apply Finset.sum_congr rfl
    intro k _
    simp only [radicalMatrix, selectionMatrix]
    cases hb : (radicalCoefficients.get k).testBit i.val <;>
      simp [hb, bit, GeneratorCertificates.bit, Nat.testBit_two_pow, Fin.ext_iff]

set_option maxRecDepth 10000 in
/-- The finite recovery identities imply the exact ten-coordinate contract. -/
theorem kernel_of_checks (h : ∀ i, RowChecks i) (c : Fin 1221 → ZMod 2)
    (hc : evaluationMatrix *ᵥ c = 0) (j : Fin 1221) :
    c j = ∑ i : Fin 10, c (radicalCoordinateIndex i) *
      bit (radicalCoefficients.get i) j.val := by
  have hd : rows 1211 recoveryRows * evaluationMatrix = rows 1221 remainderRows :=
    rows_mul _ _ _ (fun i => (h i).1)
  have hz := congrArg (fun M => M *ᵥ c) hd
  rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero,
    remainder_decode (fun i => (h i).2), Matrix.add_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, selection_mulVec] at hz
  have hj := congrFun hz j
  change 0 = c j + (radicalMatrix *ᵥ fun k => c (radicalCoordinateIndex k)) j at hj
  have hh := (eq_neg_of_add_eq_zero_left hj.symm).trans (CharTwo.neg_eq _)
  simpa only [Matrix.mulVec, dotProduct, radicalMatrix, mul_comm] using hh

end CoefficientElimination
end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
