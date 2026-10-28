module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.Mixed
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.CompletenessData

/-!
# Reduction of radical completeness to two finite certificates

Every exterior form is a coefficient sum of the original 1221 generators.
The radical condition kills the selected Eᵀ R entries. Correctness of their
coefficient table, together with its kernel reconstruction identity, therefore
expresses every radical form as a sum of the 53 checked radical forms.
Neither finite premise is asserted here. Their assembly remains a separate
obligation; see source/README.md and ../../source/README.md.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate
open GeneratorCertificates

/-- The actual radical condition kills every selected displacement evaluation. -/
theorem selectedEvaluation_zero {R : BinaryMatrix}
    (hR : R ∈ exteriorRadical displacementVectors) : selectedEvaluation R = 0 := by
  ext i
  let a := selectedRowIndices.get i
  let b := selectedColumnIndices.get i
  have hu : restrictionEmbedding *ᵥ Pi.single a 1 ∈ displacementVectors := by
    refine ⟨restrictionLifts *ᵥ Pi.single a 1, ?_⟩
    calc
      displacement (restrictionLifts *ᵥ Pi.single a 1) =
          (matrixA - 1) *ᵥ (restrictionLifts *ᵥ Pi.single a 1) := by
        simp only [displacement_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = _ := by rw [Matrix.mulVec_mulVec, restrictionEmbedding_displacement]
  have hv := hR.2 _ hu (Pi.single b 1)
  rw [formValue, dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_single_one, single_dotProduct, one_mul] at hv
  exact hv

set_option maxRecDepth 10000 in
/-- Correctness on the original generators suffices for all coefficient sums. -/
theorem selectedEvaluation_combination
    (heval : ∀ i j, selectedEvaluation (exteriorBasisForm j) i =
      coefficientEvaluationMatrix i j) (c : Fin 1221 → ZMod 2) :
    selectedEvaluation (exteriorCombination c) = coefficientEvaluationMatrix *ᵥ c := by
  change selectedEvaluation (∑ j, c j • exteriorBasisForm j) = _
  rw [map_sum]
  simp only [map_smul]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [heval, mul_comm]

set_option maxRecDepth 10000 in
/-- The coefficient columns synthesize precisely the checked radical forms. -/
theorem exteriorCombination_radical (d : Fin 53 → ZMod 2) :
    exteriorCombination (radicalCoefficientMatrix *ᵥ d) =
      ∑ k, d k • radicalGenerator k := by
  have hgen (k : Fin 53) : radicalGenerator k =
      ∑ j : Fin 1221, bit (radicalCoefficients.get k) j.val • exteriorBasisForm j := by
    rw [radicalGenerator, ← (allWitnessChecks k).1, scan_eq,
      decodeExteriorForm_combination]
    rfl
  change (∑ j : Fin 1221,
    (∑ k : Fin 53, bit (radicalCoefficients.get k) j.val * d k) • exteriorBasisForm j) = _
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [hgen, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul, mul_comm]

set_option maxRecDepth 10000 in
/-- Conditional completeness. Both concrete finite premises must be discharged. -/
theorem exteriorRadical_le_radicalSpan_of_certificates
    (heval : ∀ i j, selectedEvaluation (exteriorBasisForm j) i =
      coefficientEvaluationMatrix i j)
    (hkernel : ∀ c : Fin 1221 → ZMod 2, coefficientEvaluationMatrix *ᵥ c = 0 →
      c = radicalCoefficientMatrix *ᵥ freeCoefficients c) :
    exteriorRadical displacementVectors ≤ radicalSpan := by
  intro R hR
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hR.1
  change exteriorCombination c = R at hc
  have hz : coefficientEvaluationMatrix *ᵥ c = 0 := by
    rw [← selectedEvaluation_combination heval, hc]
    exact selectedEvaluation_zero hR
  rw [← hc, hkernel c hz, exteriorCombination_radical]
  exact radicalSpan.sum_mem (fun k _ => radicalSpan.smul_mem _
    (Submodule.subset_span ⟨k, rfl⟩))

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate
