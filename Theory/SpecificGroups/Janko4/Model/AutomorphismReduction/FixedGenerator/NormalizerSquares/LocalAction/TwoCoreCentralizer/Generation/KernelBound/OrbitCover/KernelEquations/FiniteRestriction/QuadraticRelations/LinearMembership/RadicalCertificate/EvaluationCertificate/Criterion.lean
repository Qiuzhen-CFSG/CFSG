module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.CompletenessData
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorInvariance.Basis

/-!
# Soundness of the selected evaluation certificate

The first fourteen rows of Eᵀ R contain every selected entry. Packed row
multiplication computes these rows, and a sequential bit check compares them
with the published coefficient table. The existing `basis_decode` certificate
connects each full packed matrix to the original exterior generator.
See ../source/README.md and ../../source/README.md for the finite contract
and ATLAS coordinate provenance.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate.EvaluationCertificate
open GeneratorCertificates ExteriorInvariance
set_option maxRecDepth 10000

private theorem row_bit (x : ℕ) (r : Fin 50) (j : Fin 112) :
    bit (flatMulRow (restrictionColumns.get r) x) j.val =
      (restrictionEmbeddingᵀ * flatMatrix x) r j := by
  rw [flatMulRow, bit_xorList, List.map_ofFn, List.sum_ofFn, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← flatRow_bit x k j]
  change _ = bit (restrictionColumns.get r) k.val * _
  cases h : (restrictionColumns.get r).testBit k.val <;> simp [h, bit]


/-- Sequential comparison with the published coefficient rows. -/
def checkEntries (x j : ℕ) : List (Fin 50) → List (Fin 112) → List ℕ → Bool
  | [], [], [] => true
  | r :: rs, c :: cs, w :: ws =>
      (x.testBit (112 * r.val + c.val) == w.testBit j) && checkEntries x j rs cs ws
  | _, _, _ => false

private theorem checkEntries_sound (x j : ℕ) (rs : List (Fin 50))
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
    (h : checkEntries x j selectedRowIndices.toList selectedColumnIndices.toList
      coefficientEvaluationRows.toList = true) (i : Fin 1168) :
    x.testBit (112 * (selectedRowIndices.get i).val + (selectedColumnIndices.get i).val) =
      (coefficientEvaluationRows.get i).testBit j := by
  simpa [Vector.get] using checkEntries_sound x j _ _ _ h i.val
    (by simp) (by simp) (by simp)

set_option maxHeartbeats 2000000 in
private theorem selected_row_lt (i : Fin 1168) : (selectedRowIndices.get i).val < 14 := by
  have h : selectedRowIndices.toList.all (fun r => decide (r.val < 14)) = true := by
    decide +kernel
  have hm : selectedRowIndices.get i ∈ selectedRowIndices.toList := by
    apply List.mem_iff_getElem.mpr
    exact ⟨i.val, by simp, by simp [Vector.get]⟩
  exact of_decide_eq_true ((List.all_eq_true.mp h) _ hm)

/-- Packed row products and selected-bit checks imply the actual generator contract. -/
theorem evaluation_sound (j : Fin 1221) (x : ℕ)
    (hr : ∀ r : Fin 14, flatMulRow (restrictionColumns.get ⟨r.val, by omega⟩)
      (basisFlat j.val) = flatRow x r.val)
    (he : checkEntries x j.val selectedRowIndices.toList selectedColumnIndices.toList
      coefficientEvaluationRows.toList = true) (i : Fin 1168) :
    selectedEvaluation (exteriorBasisForm j) i = coefficientEvaluationMatrix i j := by
  change (restrictionEmbeddingᵀ * exteriorBasisForm j)
    (selectedRowIndices.get i) (selectedColumnIndices.get i) = _
  rw [← basis_decode j, ← row_bit]
  rw [hr ⟨(selectedRowIndices.get i).val, selected_row_lt i⟩]
  change bit (flatRow x (selectedRowIndices.get i).val)
    (selectedColumnIndices.get i).val = bit (coefficientEvaluationRows.get i) j.val
  simp only [bit, flatRow, Nat.testBit_mod_two_pow,
    (selectedColumnIndices.get i).isLt, decide_true, Bool.true_and,
    Nat.testBit_shiftRight, selected_bits x j.val he i]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate.EvaluationCertificate
