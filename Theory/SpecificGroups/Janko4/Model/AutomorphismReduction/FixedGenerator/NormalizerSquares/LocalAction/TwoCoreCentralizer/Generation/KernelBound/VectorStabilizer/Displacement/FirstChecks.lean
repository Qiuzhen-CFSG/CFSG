module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.Arithmetic

/-!
# Fixed-column and common-eigenvector checks

The first coefficient kernel has 103 displayed generators. The common
eigenvector cuts its scalar kernel to the 102 nilpotent directions. Every
row identity is checked by the Lean kernel; the generation source is
source/generate.py and ../source/explore.py.
-/

public section
set_option Elab.async false
set_option maxRecDepth 10000
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates LinearMembership.FiniteAlgebra

set_option maxHeartbeats 5000000 in
theorem linear_words_rows (i : Fin 125) :
    slices 50 50 (linearWords.get i) = restrictionLinearRows.get i := by
  have h : ∀ k : Fin 125, ∀ j : Fin 50,
      (linearWords.get k >>> (50 * j.val)) % 2^50 =
        (restrictionLinearRows.get k).get j := by decide +kernel
  apply Vector.ext
  intro j hj
  change (slices 50 50 (linearWords.get i)).get ⟨j, hj⟩ =
    (restrictionLinearRows.get i).get ⟨j, hj⟩
  simpa only [slices, get_ofFn] using h i ⟨j, hj⟩

set_option maxHeartbeats 5000000 in
theorem identity_words :
    slices 50 50 (scan identityCoefficients linearWords.toList) =
      Vector.ofFn (fun i : Fin 50 => 2 ^ i.val) := by
  have h : ∀ i : Fin 50,
      (scan identityCoefficients linearWords.toList >>> (50 * i.val)) % 2^50 =
        2 ^ i.val := by decide +kernel
  apply Vector.ext
  intro i hi
  change (slices 50 50 _).get ⟨i, hi⟩ = (Vector.ofFn _).get ⟨i, hi⟩
  simpa only [slices, get_ofFn] using h ⟨i, hi⟩

set_option maxHeartbeats 5000000 in
theorem first_evaluation_bits : ∀ i : Fin 50, ∀ k : Fin 125,
    (firstEvaluationRows.get i).testBit k.val =
      ((restrictionLinearRows.get k).get i).testBit 0 := by decide +kernel

set_option maxHeartbeats 5000000 in
theorem first_recovery_checks : ∀ i : Fin 125,
    scan (firstRecoveryRows.get i) firstEvaluationRows.toList = firstRemainderRows.get i := by
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem first_remainder_checks : ∀ i : Fin 125,
    firstRemainderRows.get i = 2 ^ i.val ^^^
      xorList (List.ofFn (fun k : Fin 103 =>
        if (firstKernelWords.get k).testBit i.val then 2 ^ (firstFree.get k).val else 0)) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem fixed_combination_checks : ∀ i : Fin 103,
    scan (firstKernelWords.get i) linearWords.toList = fixedWords.get i := by decide +kernel

set_option maxHeartbeats 5000000 in
theorem scalar_recovery_checks : ∀ i : Fin 103,
    scan (scalarRecoveryRows.get i) scalarEvaluationRows.toList = scalarRemainderRows.get i := by
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem scalar_remainder_checks : ∀ i : Fin 103,
    scalarRemainderRows.get i = 2 ^ i.val ^^^
      xorList (List.ofFn (fun k : Fin 102 =>
        if (scalarKernelWords.get k).testBit i.val then 2 ^ (scalarFree.get k).val else 0)) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem scalar_evaluation_bits : ∀ i : Fin 103,
    (scalarEvaluationRows.get 0).testBit i.val = (eigenvalueWords.get i).testBit 0 := by
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem nil_combination_checks : ∀ i : Fin 102,
    scan (scalarKernelWords.get i) fixedWords.toList = nilWords.get i := by decide +kernel

set_option maxHeartbeats 5000000 in
theorem eigenvector_rows : ∀ i : Fin 50,
    (eigenvectorRows.get i).testBit 0 = eigenvectorWord.testBit i.val := by decide +kernel

theorem eigenvector_nonzero : eigenvector ≠ 0 := by
  intro h
  have := congrFun h (0 : Fin 50)
  norm_num [eigenvector, eigenvectorWord, bit] at this

set_option maxHeartbeats 5000000 in
theorem eigenvector_checks : ∀ k : Fin 103, ∀ i : Fin 50,
    scan ((slices 50 50 (fixedWords.get k)).get i) eigenvectorRows.toList =
      if (eigenvalueWords.get k).testBit 0 then eigenvectorRows.get i else 0 := by
  simp only [slices, get_ofFn]
  decide +kernel

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement
