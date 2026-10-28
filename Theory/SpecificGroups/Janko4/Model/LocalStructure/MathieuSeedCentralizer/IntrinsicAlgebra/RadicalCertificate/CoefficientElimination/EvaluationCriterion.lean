module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.CoefficientElimination.Tables

/-!
# Interpret the selected radical equations

For each original exterior form we check thirteen rows of Kᵀ R and then
compare 1211 selected bits with the coefficient table. Symmetry of ambient
forms transports R K = 0 to precisely these equations. See source/README.md.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open ExteriorInvariance
namespace CoefficientElimination

def selectedKernelRow (i : Fin 1211) : Fin 56 :=
  ⟨(selectedRows.get i).val, by have h := (selectedRows.get i).isLt; omega⟩

def selectedEvaluation : BinaryMatrix →ₗ[ZMod 2] (Fin 1211 → ZMod 2) where
  toFun R i := (kernelColumnsᵀ * R) (selectedKernelRow i) (selectedColumns.get i)
  map_add' R S := by ext i; simp [Matrix.mul_add]
  map_smul' c R := by ext i; simp [Matrix.mul_smul]

def evaluationMatrix : Matrix (Fin 1211) (Fin 1221) (ZMod 2) := rows 1221 evaluationRows

/-- Sequential bit comparison avoids repeated indexed list traversal. -/
def checkEntries (x j : ℕ) : List (Fin 13) → List (Fin 112) → List ℕ → Bool
  | [], [], [] => true
  | r :: rs, c :: cs, w :: ws =>
      (x.testBit (112 * r.val + c.val) == w.testBit j) && checkEntries x j rs cs ws
  | _, _, _ => false

private theorem checkEntries_sound (x j : ℕ) (rs : List (Fin 13))
    (cs : List (Fin 112)) (ws : List ℕ) (h : checkEntries x j rs cs ws = true)
    (i : ℕ) (hr : i < rs.length) (hc : i < cs.length) (hw : i < ws.length) :
    x.testBit (112 * rs[i].val + cs[i].val) = ws[i].testBit j := by
  induction rs generalizing cs ws i with
  | nil => simp at hr
  | cons r rs ih =>
    cases cs with
    | nil => simp at hc
    | cons c cs =>
      cases ws with
      | nil => simp at hw
      | cons w ws =>
        simp only [checkEntries, Bool.and_eq_true, beq_iff_eq] at h
        cases i with
        | zero => exact h.1
        | succ i =>
          exact ih cs ws h.2 i (by simpa using hr)
            (by simpa using hc) (by simpa using hw)

private theorem selected_bits (x j : ℕ)
    (h : checkEntries x j selectedRows.toList selectedColumns.toList
      evaluationRows.toList = true) (i : Fin 1211) :
    x.testBit (112 * (selectedRows.get i).val + (selectedColumns.get i).val) =
      (evaluationRows.get i).testBit j := by
  simpa [Vector.get] using checkEntries_sound x j _ _ _ h i.val
    (by simp) (by simp) (by simp)

/-- Every numerical premise is discharged separately in `Evaluations`. -/
theorem evaluation_sound (j : Fin 1221) (x : ℕ)
    (hr : ∀ r : Fin 13, flatMulRow (adaptedColumns.get ⟨r.val, by omega⟩)
      (basisFlat j.val) = flatRow x r.val)
    (he : checkEntries x j.val selectedRows.toList selectedColumns.toList
      evaluationRows.toList = true) (i : Fin 1211) :
    selectedEvaluation (exteriorBasisForm j) i = evaluationMatrix i j := by
  change (kernelColumnsᵀ * exteriorBasisForm j)
    (selectedKernelRow i) (selectedColumns.get i) = _
  rw [← basis_decode j, ← kernel_row_bit]
  rw [show firstIndex (selectedKernelRow i) =
    (⟨(selectedRows.get i).val, by have h := (selectedRows.get i).isLt; omega⟩ : Fin 112)
    from rfl, hr (selectedRows.get i)]
  change bit (flatRow x (selectedRows.get i).val)
    (selectedColumns.get i).val = bit (evaluationRows.get i) j.val
  simp only [bit, flatRow, Nat.testBit_mod_two_pow,
    (selectedColumns.get i).isLt, decide_true, Bool.true_and,
    Nat.testBit_shiftRight, selected_bits x j.val he i]

theorem selectedEvaluation_zero {R : BinaryMatrix} (hR : R ∈ rawRadicalForms) :
    selectedEvaluation R = 0 := by
  have hz := congrArg Matrix.transpose hR.2
  rw [Matrix.transpose_mul, ambientForms_transpose hR.1, Matrix.transpose_zero] at hz
  ext i
  change (kernelColumnsᵀ * R) _ _ = 0
  rw [hz]
  rfl

set_option maxRecDepth 10000 in
theorem selectedEvaluation_sum
    (he : ∀ j i, selectedEvaluation (exteriorBasisForm j) i = evaluationMatrix i j)
    (c : Fin 1221 → ZMod 2) :
    selectedEvaluation (∑ j, c j • exteriorBasisForm j) = evaluationMatrix *ᵥ c := by
  rw [map_sum]
  simp only [map_smul]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [he, mul_comm]

end CoefficientElimination
end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
