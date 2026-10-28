module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation.Blocks

/-!
# Suzuki Gauss factorization on the five-dimensional block

The literal middle-root matrices preserve coordinates `[5,6,7,8,9]`.
We compute both signed four-root words on all five coordinates, retaining
both the short-root quadratic terms and the middle row's coupling to the
other coordinates. The panel word reverses the coordinates. Its two coroot
factors are diagonal, with weights `π(n)⁻¹, π(n)/n², 1, n²/π(n), π(n)`.

The norm, reciprocal-parameter and theta identities reduce every entry of
Gauss factorization to field algebra in characteristic two. The coroot
multiplication is checked over an abstract field before specialization to
keep the concrete coefficient-field instances out of that calculation.
No quotient or faithfulness inference is used.

Source: GLS3, Table 2.4 type V, 2.3.4--8 and 2.6.5,
`refs/KGroup/GLS3/chapter2.tex`; the literal supports in `Ambient.Tables`
and the scalar identities in `Gauss.Coordinates`.
-/

namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation
namespace FiveBlock
open BlockParameters.FieldRecovery
open scoped Matrix
set_option linter.unusedSimpArgs false
noncomputable section
variable {R : Type*} [Field R]

def simple_true_0 (t : R) : Matrix (Fin 5) (Fin 5) R :=
  !![1, 0, 0, 0, 0;
    t, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, t, 1]

lemma blockSimple_true_0 (t : R) : blockSimple 1 true 0 t = simple_true_0 t := by
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [blockSimple, blockCoord, simpleMatrix, simpleIndex, incidence,
      linearSupport, quadraticSupport, simple_true_0]

def simple_true_1 (t : R) : Matrix (Fin 5) (Fin 5) R :=
  !![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, t, 1, 0, 0;
    0, t^2, 0, 1, 0;
    0, 0, 0, 0, 1]

lemma blockSimple_true_1 (t : R) : blockSimple 1 true 1 t = simple_true_1 t := by
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [blockSimple, blockCoord, simpleMatrix, simpleIndex, incidence,
      linearSupport, quadraticSupport, simple_true_1]

def simple_false_0 (t : R) : Matrix (Fin 5) (Fin 5) R :=
  !![1, t, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, t;
    0, 0, 0, 0, 1]

lemma blockSimple_false_0 (t : R) : blockSimple 1 false 0 t = simple_false_0 t := by
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [blockSimple, blockCoord, simpleMatrix, simpleIndex, incidence,
      linearSupport, quadraticSupport, simple_false_0]

def simple_false_1 (t : R) : Matrix (Fin 5) (Fin 5) R :=
  !![1, 0, 0, 0, 0;
    0, 1, 0, t^2, 0;
    0, 0, 1, t, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1]

lemma blockSimple_false_1 (t : R) : blockSimple 1 false 1 t = simple_false_1 t := by
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [blockSimple, blockCoord, simpleMatrix, simpleIndex, incidence,
      linearSupport, quadraticSupport, simple_false_1]

variable [CharP R 2]

def reflection_0 : Matrix (Fin 5) (Fin 5) R :=
  !![0, 1, 0, 0, 0;
    1, 0, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 0, 1;
    0, 0, 0, 1, 0]

lemma blockReflection_0 : blockReflection (R := R) 1 0 = reflection_0 := by
  rw [blockReflection, blockWeyl, blockSimple_true_0, blockSimple_false_0]
  simp only [inv_one]
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [simple_true_0, simple_false_0, reflection_0, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, CharTwo.add_self_eq_zero, CharTwo.ofNat_eq_mod]

def reflection_1 : Matrix (Fin 5) (Fin 5) R :=
  !![1, 0, 0, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 1, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 0, 0, 1]

lemma blockReflection_1 : blockReflection (R := R) 1 1 = reflection_1 := by
  rw [blockReflection, blockWeyl, blockSimple_true_1, blockSimple_false_1]
  simp only [inv_one]
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [simple_true_1, simple_false_1, reflection_1, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, CharTwo.add_self_eq_zero, CharTwo.ofNat_eq_mod]

def root_true_2 (t : R) : Matrix (Fin 5) (Fin 5) R :=
  !![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    t, 0, 0, 1, 0;
    0, t, 0, 0, 1]

lemma blockRoot_true_2 (t : R) : blockRoot 1 true 2 t = root_true_2 t := by
  change blockReflection 1 1 * blockSimple 1 true 0 t * blockReflection 1 1 = _
  rw [blockReflection_1, blockSimple_true_0]
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [reflection_1, simple_true_0, root_true_2, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]

def root_true_3 (t : R) : Matrix (Fin 5) (Fin 5) R :=
  !![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    t, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    t^2, 0, 0, 0, 1]

lemma blockRoot_true_3 (t : R) : blockRoot 1 true 3 t = root_true_3 t := by
  change blockReflection 1 0 * blockSimple 1 true 1 t * blockReflection 1 0 = _
  rw [blockReflection_0, blockSimple_true_1]
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [reflection_0, simple_true_1, root_true_3, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]

def root_false_2 (t : R) : Matrix (Fin 5) (Fin 5) R :=
  !![1, 0, 0, t, 0;
    0, 1, 0, 0, t;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1]

lemma blockRoot_false_2 (t : R) : blockRoot 1 false 2 t = root_false_2 t := by
  change blockReflection 1 1 * blockSimple 1 false 0 t * blockReflection 1 1 = _
  rw [blockReflection_1, blockSimple_false_0]
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [reflection_1, simple_false_0, root_false_2, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]

def root_false_3 (t : R) : Matrix (Fin 5) (Fin 5) R :=
  !![1, 0, 0, 0, t^2;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, t;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1]

lemma blockRoot_false_3 (t : R) : blockRoot 1 false 3 t = root_false_3 t := by
  change blockReflection 1 0 * blockSimple 1 false 1 t * blockReflection 1 0 = _
  rw [blockReflection_0, blockSimple_false_1]
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [reflection_0, simple_false_1, root_false_3, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]

lemma blockPanel_matrix : blockPanel (R := R) 1 =
    !![0,0,0,0,1; 0,0,0,1,0; 0,0,1,0,0; 0,1,0,0,0; 1,0,0,0,0] := by
  rw [blockPanel, blockReflection_0, blockReflection_1]
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [reflection_0, reflection_1, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

lemma blockCoroot_0 (t : R) (ht : t ≠ 0) :
    blockWeyl 1 0 t * blockReflection 1 0 =
    !![t⁻¹, 0, 0, 0, 0;
    0, t, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, t⁻¹, 0;
    0, 0, 0, 0, t] := by
  rw [blockWeyl, blockSimple_true_0, blockSimple_false_0, blockReflection_0]
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [simple_true_0, simple_false_0, reflection_0, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, ht, CharTwo.add_self_eq_zero]

lemma blockCoroot_1 (t : R) (ht : t ≠ 0) :
    blockWeyl 1 1 t * blockReflection 1 1 =
    !![1, 0, 0, 0, 0;
    0, (t⁻¹)^2, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, t^2, 0;
    0, 0, 0, 0, 1] := by
  rw [blockWeyl, blockSimple_true_1, blockSimple_false_1, blockReflection_1]
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [simple_true_1, simple_false_1, reflection_1, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, ht, CharTwo.add_self_eq_zero]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]

lemma blockCoroot_product (t s : R) (ht : t ≠ 0) (hs : s ≠ 0) :
    (blockWeyl 1 0 t * blockReflection 1 0) *
      (blockWeyl 1 1 s * blockReflection 1 1) =
    !![t⁻¹,0,0,0,0; 0,t / s^2,0,0,0; 0,0,1,0,0;
      0,0,0,s^2 / t,0; 0,0,0,0,t] := by
  have h := congrArg₂
    (fun A B : Matrix (Fin (blockSize 1)) (Fin (blockSize 1)) R => A * B)
    (blockCoroot_0 t ht) (blockCoroot_1 s hs)
  refine h.trans ?_
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, div_eq_mul_inv, mul_comm]

variable {m : ℕ}

lemma blockTorus_matrix (n : (CoefficientField m)ˣ) :
    blockTorus 1 n =
    !![(titsEnd m (n : CoefficientField m))⁻¹,0,0,0,0;
      0,titsEnd m (n : CoefficientField m) / (n : CoefficientField m)^2,0,0,0;
      0,0,1,0,0;
      0,0,0,(n : CoefficientField m)^2 / titsEnd m (n : CoefficientField m),0;
      0,0,0,0,titsEnd m (n : CoefficientField m)] :=
  blockCoroot_product _ _ ((map_ne_zero (titsEnd m)).mpr n.ne_zero) n.ne_zero

lemma blockWord_positive_matrix (t u : CoefficientField m) :
    blockWord 1 true t u =
    !![1,0,0,0,0;
      t,1,0,0,0;
      t * theta m t + theta m u,theta m t,1,0,0;
      u,(theta m t)^2,0,1,0;
      titsEnd m (norm t u),t * (theta m t)^2 + u,0,t,1] := by
  unfold blockWord
  rw [blockRoot_true_2, blockRoot_true_3]
  change blockSimple 1 true 0 t * blockSimple 1 true 1 (theta m t) * _ * _ = _
  rw [blockSimple_true_0, blockSimple_true_1]
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [simple_true_0, simple_true_1, root_true_2, root_true_3,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, tits_norm]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]

lemma blockWord_negative_matrix (t u : CoefficientField m) :
    blockWord 1 false t u =
    !![1,t,0,t * (theta m t)^2 + u,titsEnd m (norm t u);
      0,1,0,(theta m t)^2,u;
      0,0,1,theta m t,t * theta m t + theta m u;
      0,0,0,1,t;
      0,0,0,0,1] := by
  unfold blockWord
  rw [blockRoot_false_2, blockRoot_false_3]
  change blockSimple 1 false 0 t * blockSimple 1 false 1 (theta m t) * _ * _ = _
  rw [blockSimple_false_0, blockSimple_false_1]
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [simple_false_0, simple_false_1, root_false_2, root_false_3,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, tits_norm]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]

lemma gauss (t u : CoefficientField m) (hn : norm t u ≠ 0) :
    blockPanel 1 * blockWord 1 false t u =
      blockWord 1 false (negativeFirst t u) (negativeSecond t u) *
        blockTorus 1 (Units.mk0 (norm t u) hn) *
          blockWord 1 true (positiveFirst t u) (positiveSecond t u) := by
  rw [blockPanel_matrix, blockWord_negative_matrix, blockWord_negative_matrix,
    blockWord_positive_matrix, blockTorus_matrix,
    theta_negativeFirst, theta_negativeSecond, norm_negative t u hn,
    theta_positiveFirst, theta_positiveSecond, norm_positive t u hn]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [Units.val_mk0, map_inv₀, positiveSecond, positiveFirst,
    negativeFirst, negativeSecond, map_add, map_mul, map_div₀, titsEnd_twice]
  dsimp +instances only [blockSize, Matrix.cons_val_one, Matrix.cons_val_zero]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  all_goals field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]

end
end FiveBlock

/-- The complete Gauss equation on coordinates `[5,6,7,8,9]`. -/
public theorem blockGauss_fiveDimensional (m : ℕ) : BlockGauss m 1 := by
  intro t u hn
  exact FiveBlock.gauss t u hn

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation
