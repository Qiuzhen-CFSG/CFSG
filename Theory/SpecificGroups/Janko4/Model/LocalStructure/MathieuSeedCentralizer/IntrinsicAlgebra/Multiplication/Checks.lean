module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.OperatorChecks
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.MonomialChecks

/-!
# Kernel certificates for the seed multiplication witnesses

Every numerical assertion here uses Lean's kernel evaluator. Products are
checked row by row with the sound XOR algorithm of `Packed`. The 56 selected
monomials and the exact saved basis both have invertible evaluation matrices.
These identities do not assume a rank, a grading, or a group identification.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open MultiplicationCertificate


namespace MultiplicationCertificate

set_option maxRecDepth 100000 in
theorem basisParents_lt (i : Fin 55) : (basisParents.get i).val < i.succ.val := by
  have h : ∀ i : Fin 55, (basisParents.get i).val < i.succ.val := by decide +kernel
  exact h i

set_option maxRecDepth 100000 in
theorem basisTuples_step (i : Fin 55) :
    basisTuples.get i.succ = basisHeads.get i :: basisTuples.get (basisParents.get i) := by
  have h : ∀ i : Fin 55,
      basisTuples.get i.succ = basisHeads.get i :: basisTuples.get (basisParents.get i) := by
    decide +kernel
  exact h i

set_option maxRecDepth 100000 in
theorem basisSet_sort (i : Fin 56) : (basisSet i).sort (· ≤ ·) = basisTuples.get i := by
  have h : ∀ i : Fin 56, (basisTuples.get i).Nodup ∧
      (basisTuples.get i).Pairwise (· ≤ ·) := by decide +kernel
  exact (List.toFinset_sort _ (h i).1).mpr (h i).2

set_option maxRecDepth 100000 in
theorem algebraBasis_expansion (i : Fin 56) :
    algebraBasis i = ∑ j : Fin 56, bit (savedCoordinates.get i) j.val • gradedBasis j := by
  have h : ∀ i : Fin 56,
      combination basisWords (savedCoordinates.get i) = algebraBasisWords.get i := by decide +kernel
  change decodeFlat (algebraBasisWords.get i) = _
  rw [← h i, decode_combination]
  rfl

set_option maxRecDepth 100000 in
theorem savedEvaluation_entry (i j : Fin 56) :
    decodeFlat savedEvaluationWord i j = algebraBasis j i 0 := by
  have h : ∀ i j : Fin 56, savedEvaluationWord.testBit (56*i.val+j.val) =
      (algebraBasisWords.get j).testBit (56*i.val) := by decide +kernel
  simp only [decodeFlat, algebraBasis, bit, Fin.val_zero, Nat.add_zero, h]

set_option maxRecDepth 100000 in
theorem gradedEvaluation_entry (i j : Fin 56) :
    decodeFlat gradedEvaluationWord i j = gradedBasis j i 0 := by
  have h : ∀ i j : Fin 56, gradedEvaluationWord.testBit (56*i.val+j.val) =
      (basisWords.get j).testBit (56*i.val) := by decide +kernel
  simp only [decodeFlat, gradedBasis, bit, Fin.val_zero, Nat.add_zero, h]

set_option maxRecDepth 100000 in
theorem savedEvaluation_inverse_mul :
    decodeFlat savedEvaluationInverseWord * decodeFlat savedEvaluationWord = 1 := by
  apply Eq.trans (flat_mul_eq _ _ (basisWords.get 0) (by decide +kernel))
  exact gradedBasis_zero

set_option maxRecDepth 100000 in
theorem savedEvaluation_mul_inverse :
    decodeFlat savedEvaluationWord * decodeFlat savedEvaluationInverseWord = 1 := by
  apply Eq.trans (flat_mul_eq _ _ (basisWords.get 0) (by decide +kernel))
  exact gradedBasis_zero

set_option maxRecDepth 100000 in
theorem gradedEvaluation_inverse_mul :
    decodeFlat gradedEvaluationInverseWord * decodeFlat gradedEvaluationWord = 1 := by
  apply Eq.trans (flat_mul_eq _ _ (basisWords.get 0) (by decide +kernel))
  exact gradedBasis_zero

set_option maxRecDepth 100000 in
theorem gradedEvaluation_mul_inverse :
    decodeFlat gradedEvaluationWord * decodeFlat gradedEvaluationInverseWord = 1 := by
  apply Eq.trans (flat_mul_eq _ _ (basisWords.get 0) (by decide +kernel))
  exact gradedBasis_zero

end MultiplicationCertificate
end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
