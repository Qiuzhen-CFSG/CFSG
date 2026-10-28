module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.RadicalK.Kernel
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.RadicalK.UpperBlocks

/-!
# The radical-K upper-block span

Since im(A-1) is contained in ker(A-1), an exterior form annihilating the
fixed space lies in the already certified 53-generator radical-I span. Its
mixed evaluation vanishes because the H columns are fixed. The complete
mixed coefficient kernel then expresses it as a combination of thirteen
forms whose upper blocks are exactly the shared radicalKGenerator matrices.

This proves the explicit finite premise used by the off-diagonal and shear
reductions. It asserts neither a dimension nor a group-identification result.
Matrix provenance and source motivation: VectorStabilizer/source/README.md;
reproduction and the certificate identities: RadicalK/source/README.md.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open OrbitCoverCoordinates.LinearMembership.RadicalCertificate RadicalK

private theorem radical_fixed_mixed_zero (R : BinaryMatrix)
    (hR : R ∈ exteriorRadical fixedVectors) : mixedEvaluation R = 0 := by
  have hrows : mixedEmbeddingᵀ * R = 0 := by
    ext i j
    have hv := hR.2 (fun k => mixedEmbedding k i) (mixedEmbedding_col_mem_fixed i)
      (Pi.single j 1)
    have he : ((mixedEmbeddingᵀ * R) *ᵥ Pi.single j 1) i =
        formValue R (fun k => mixedEmbedding k i) (Pi.single j 1) := by
      rw [← Matrix.mulVec_mulVec]
      rfl
    rw [Matrix.mulVec_single_one] at he
    exact he.trans hv
  change mixedEmbeddingᵀ * R * restrictionLifts = 0
  rw [hrows, Matrix.zero_mul]

/-- Every actual radical-K form has its UU block in the thirteen literal
matrices' span, with all completeness premises discharged. -/
theorem radicalK_upper : RadicalKUpperBound := by
  intro R hR
  have hI : R ∈ exteriorRadical displacementVectors :=
    ⟨hR.1, fun u hu v => hR.2 u (displacementVectors_le_fixedVectors hu) v⟩
  rw [exteriorRadical_eq_radicalSpan] at hI
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hI
  change radicalCombination c = R at hc
  have hm : mixedEvaluation (radicalCombination c) = 0 := by
    rw [hc]
    exact radical_fixed_mixed_zero R hR
  rw [← hc, mixed_kernel c hm, radicalCombination_kernel]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    kernelForm_upper]
  exact radicalKUpperSpace.sum_mem (fun i _ => radicalKUpperSpace.smul_mem _
    (Submodule.subset_span ⟨i, rfl⟩))

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
