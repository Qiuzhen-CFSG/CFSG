module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.RadicalK.Data

/-!
# Complete mixed coefficient kernel

The checked identity D T = 1 + K F reconstructs every coefficient vector
whose selected mixed evaluations vanish. The thirteen columns of K have
zero full mixed evaluation, so this proves completeness for the actual mixed
map, not merely for its selected rows. The same coefficients synthesize the
thirteen explicit ambient exterior forms. See source/README.md.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.RadicalK
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open OrbitCoverCoordinates.LinearMembership.RadicalCertificate GeneratorCertificates

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem test_checks : ∀ i : Fin 40, ∀ j : Fin 53,
    (testRows.get i).testBit j.val =
      ((radicalMixedRows.get j).get (testRowIndices.get i)).testBit
        (testColumnIndices.get i).val := by decide +kernel

private theorem test_combination (c : Fin 53 → ZMod 2) :
    testMatrix *ᵥ c = fun i => mixedEvaluation (radicalCombination c)
      (testRowIndices.get i) (testColumnIndices.get i) := by
  unfold radicalCombination
  rw [map_sum]
  simp only [map_smul, radicalGenerator_mixed]
  ext i
  simp only [Matrix.mulVec, dotProduct, testMatrix, rectDecode,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [bit, test_checks, mul_comm]

private def selectionMatrix : Matrix (Fin 13) (Fin 53) (ZMod 2) :=
  fun k j => if freeIndices.get k = j then 1 else 0

private theorem selection_mulVec (c : Fin 53 → ZMod 2) :
    selectionMatrix *ᵥ c = freeValues c := by
  ext k
  simp [Matrix.mulVec, dotProduct, selectionMatrix, freeValues]

private def remainderWord (i : Fin 53) : ℕ :=
  2 ^ i.val ^^^ xorList (List.ofFn (fun k : Fin 13 =>
    if (kernelWords.get k).testBit i.val
    then 2 ^ (freeIndices.get k).val else 0))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem recovery_checks : ∀ i : Fin 53,
    scan (recoveryRows.get i) testRows.toList = remainderRows.get i ∧
    remainderRows.get i = remainderWord i := by decide +kernel

private theorem remainder_decode :
    rectDecode 53 remainderRows = 1 + kernelMatrix * selectionMatrix := by
  ext i j
  simp only [rectDecode, (recovery_checks _).2, remainderWord, bit_xor, bit_xorList,
    List.map_ofFn, List.sum_ofFn, Matrix.add_apply, Matrix.mul_apply]
  apply congrArg₂ (· + ·)
  · simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
  · apply Finset.sum_congr rfl
    intro k _
    simp only [kernelMatrix, Matrix.transpose_apply, rectDecode, selectionMatrix]
    cases hb : (kernelWords.get k).testBit i.val <;>
      simp [hb, bit, Nat.testBit_two_pow, Fin.ext_iff]

/-- Every vector killed by the actual mixed evaluation is reconstructed from
its thirteen free coefficients. -/
theorem mixed_kernel (c : Fin 53 → ZMod 2)
    (hc : mixedEvaluation (radicalCombination c) = 0) :
    c = kernelMatrix *ᵥ freeValues c := by
  have ht : testMatrix *ᵥ c = 0 := by rw [test_combination, hc]; rfl
  have hd : rectDecode 40 recoveryRows * testMatrix = rectDecode 53 remainderRows := by
    apply rectProduct_eq
    intro i
    rw [← scan_eq]
    exact (recovery_checks i).1
  have hz := congrArg (fun M => M *ᵥ c) hd
  rw [← Matrix.mulVec_mulVec, ht, Matrix.mulVec_zero, remainder_decode,
    Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, selection_mulVec] at hz
  ext i
  have hi := congrFun hz i
  change 0 = c i + (kernelMatrix *ᵥ freeValues c) i at hi
  exact (eq_neg_of_add_eq_zero_left hi.symm).trans (CharTwo.neg_eq _)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem word_checks : ∀ i : Fin 13,
    scan (kernelWords.get i) radicalFormWords.toList = ambientWords.get i := by
  decide +kernel

/-- The ambient words are exactly the combinations specified by the kernel columns. -/
theorem kernelForm_combination (i : Fin 13) :
    kernelForm i = ∑ j : Fin 53, bit (kernelWords.get i) j.val • radicalGenerator j := by
  rw [kernelForm, ← word_checks i, scan_eq, decodeExteriorForm_combination]
  rfl

/-- Coefficient reconstruction commutes with synthesis of ambient forms. -/
theorem radicalCombination_kernel (d : Fin 13 → ZMod 2) :
    radicalCombination (kernelMatrix *ᵥ d) = ∑ k, d k • kernelForm k := by
  change (∑ j : Fin 53,
    (∑ k : Fin 13, bit (kernelWords.get k) j.val * d k) • radicalGenerator j) = _
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [kernelForm_combination, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul, mul_comm]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem mixed_zero_checks : ∀ i : Fin 13, ∀ r : Fin 12,
    scan (kernelWords.get i)
      (List.ofFn (fun j : Fin 53 => (radicalMixedRows.get j).get r)) = 0 := by
  decide +kernel

/-- All thirteen kernel columns vanish on every mixed entry. -/
theorem kernelForm_mixed_zero (i : Fin 13) : mixedEvaluation (kernelForm i) = 0 := by
  rw [kernelForm_combination, map_sum]
  simp only [map_smul, radicalGenerator_mixed]
  rw [← rectDecode_combination]
  ext r s
  change bit ((Vector.ofFn (fun r : Fin 12 =>
    rectRowProduct (kernelWords.get i)
      (Vector.ofFn (fun j : Fin 53 => (radicalMixedRows.get j).get r)))).get r) s.val = 0
  rw [get_ofFn, ← scan_eq, Vector.toList_ofFn, mixed_zero_checks]
  simp [bit]

/-- The complete kernel of the actual 53-form mixed evaluation. -/
theorem mixed_kernel_iff (c : Fin 53 → ZMod 2) :
    mixedEvaluation (radicalCombination c) = 0 ↔ ∃ d, c = kernelMatrix *ᵥ d := by
  constructor
  · intro hc
    exact ⟨freeValues c, mixed_kernel c hc⟩
  · rintro ⟨d, rfl⟩
    rw [radicalCombination_kernel, map_sum]
    simp only [map_smul, kernelForm_mixed_zero, smul_zero, Finset.sum_const_zero]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.RadicalK
