module
public import Theory.Representation.OrthogonalFourPlusMatrix.NormalizerNonFF
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.Representation.OrthogonalFourPlusMatrix.HyperplaneFixed

/-!
# A quantitative bound for the binary determinant normalizer

Every nontrivial elementary actor in the full normalizer has four times
its rank at most three times its fixed codimension. The existing rank-four
bound gives codimension at least six; for ranks at most three, strict
non-FF suffices. Taking the infimum over quadratic actors gives ratio≥4/3.

The binary polar pairing also identifies the base determinant action with
its dual. This transports normal-model arguments to a dual ambient action
without requiring the ambient normalizer to preserve that pairing.

Source: Aschbacher--Smith, H.1.1 and the tensor case of D.3.9, printed
pp.378 and199--200; applied to the original tensor branch in9.2.7.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped ENNReal
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

local instance : Finite (Module.End (ZMod 2) V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

theorem four_rank_le_three_fixedCodim (A : Subgroup (linearNormalizer action))
    (hA : IsElementaryTwo A) :
    4 * rank A ≤ 3 * fixedCodim (normalizerRepresentation action) A := by
  have hr := elementary_normalizer_rank_le_four A hA
  by_cases hfour : 4 ≤ rank A
  · have hc := fixedCodim_ge_six_of_rank_ge_four A hA hfour
    omega
  have hc := normalizer_rank_lt_fixedCodim A hA
  omega

theorem four_thirds_le_normalizer_quadraticRatio :
    (4 / 3 : ℝ≥0∞) ≤ quadraticRatio (normalizerRepresentation action) := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA,_⟩
  have hr : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast hA.rank_pos.ne'
  rw [actionRatio, ENNReal.le_div_iff_mul_le (Or.inl hr) (Or.inl (by simp))]
  have h := four_rank_le_three_fixedCodim A hA
  have he : (4 : ℝ≥0∞) * rank A ≤ 3 * fixedCodim (normalizerRepresentation action) A := by
    exact_mod_cast h
  calc
    4 / 3 * (rank A : ℝ≥0∞) = (4 * (rank A : ℝ≥0∞)) / 3 :=
      (ENNReal.mul_div_right_comm).symm
    _ ≤ (3 * (fixedCodim (normalizerRepresentation action) A : ℝ≥0∞)) / 3 :=
      ENNReal.div_le_div_right he _
    _ = fixedCodim (normalizerRepresentation action) A := by
      rw [mul_comm, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]

noncomputable def actionSelfDual : action.Equiv action.dual :=
  .mk (LinearEquiv.ofBijective HyperplaneFixed.pairing
    ⟨HyperplaneFixed.pairing_injective,HyperplaneFixed.pairing_surjective⟩) (fun g => by
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      change HyperplaneFixed.pairing (action g v) w =
        HyperplaneFixed.pairing v (action g⁻¹ w)
      have h := HyperplaneFixed.pairing_action g v (action g⁻¹ w)
      rw [Representation.self_inv_apply] at h
      exact h)

end ClassicalOrthogonal.FourPlusMatrix.Binary
