module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation.CartanBlock.Roots
/-!
# Full Suzuki word, panel, and torus entries on the Cartan block

The four root factors are multiplied in their literal order. Their coefficients
are then expressed using the original parameters, the Suzuki norm, and its Tits
image. Separate calculations retain the full panel (including its Cartan shear)
and identify the prescribed two-coroot word with its diagonal entries.

All comparisons hold on the entire 12-dimensional block. In particular they
include the Cartan columns, rather than just the eight root coordinates.

Source: GLS3, Table 2.4 type V, 2.3.4--8 and 2.6.5,
`refs/KGroup/GLS3/chapter2.tex`; `Gauss.Coordinates` for the norm identities.
-/

namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation.CartanBlock
open BlockParameters.FieldRecovery
open scoped Matrix
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
variable {m : ℕ}
private def wordtrue_2 (t a : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,(t * a ^ 2),0,t,0,0,0,0,0;
      0,0,1,0,0,0,0,a,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,a,1,0,0,0,0,0,0;
      0,0,0,0,a ^ 2,0,1,0,0,0,0,0;
      0,0,0,0,(a * t),t,0,1,0,0,0,0;
      0,a,0,a,0,0,0,a ^ 2,1,0,0,0;
      t,0,0,0,(a ^ 2 * t ^ 2),0,t ^ 2,0,0,1,0,0;
      0,(a * t),0,(a * t),0,0,0,(t * a ^ 2),t,a,1,0;
      0,0,0,0,0,0,0,0,0,a ^ 2,0,1]

private lemma wordtrue_2_eq (t a : CoefficientField m) :
    simple_true_0 t * simple_true_1 a = wordtrue_2 t a := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [simple_true_0, simple_true_1, wordtrue_2, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private def wordtrue_3 (t a u : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,(u + (t * a ^ 2)),0,t,0,0,0,0,0;
      0,0,1,0,u,0,0,a,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,a,1,0,0,0,0,0,0;
      0,0,0,0,a ^ 2,0,1,0,0,0,0,0;
      0,0,0,0,(a * t),t,0,1,0,0,0,0;
      0,a,0,a,(a * u),u,0,a ^ 2,1,0,0,0;
      t,0,0,0,(a ^ 2 * t ^ 2),0,t ^ 2,0,0,1,0,0;
      0,(a * t),0,(a * t),(a * t * u),(t * u),0,(u + (t * a ^ 2)),t,a,1,0;
      u,0,0,0,u ^ 2,0,0,0,0,a ^ 2,0,1]

private lemma wordtrue_3_eq (t a u : CoefficientField m) :
    wordtrue_2 t a * root_true_2 u = wordtrue_3 t a u := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [wordtrue_2, root_true_2, wordtrue_3, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private def wordtrue_4 (t a u b : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,(u + (t * a ^ 2)),0,t,0,0,0,0,0;
      0,0,1,0,(u + (a * b) + (t * a ^ 2)),(b + (a * t)),0,a,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,a,1,0,0,0,0,0,0;
      0,0,0,0,a ^ 2,0,1,0,0,0,0,0;
      0,0,0,0,b,t,0,1,0,0,0,0;
      0,a,0,a,((a * u) + (b * a ^ 2) + (t * a ^ 3)),u,(b + (a * t)),a ^ 2,1,0,0,0;
      t,0,0,0,b ^ 2,0,t ^ 2,0,0,1,0,0;
      (b + (a * t)),b,0,b,((a * b ^ 2) + (b * u) + (b * t * a ^ 2)),(b ^ 2 + (t * u) + (a ^ 2 * t ^ 2)),((a * t ^ 2) + (b * t)),(u + (t * a ^ 2)),t,a,1,0;
      u,0,0,0,(u ^ 2 + (a ^ 2 * b ^ 2) + (a ^ 4 * t ^ 2)),0,(b ^ 2 + (a ^ 2 * t ^ 2)),0,0,a ^ 2,0,1]

private lemma wordtrue_4_eq (t a u b : CoefficientField m) :
    wordtrue_3 t a u * root_true_3 (t*a+b) = wordtrue_4 t a u b := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [wordtrue_3, root_true_3, wordtrue_4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private def wordfalse_2 (t a : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,t,0,(t * a ^ 2);
      0,0,1,0,0,0,0,0,a,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,a ^ 2,0,0,0,0,0;
      0,(a * t),0,(a * t),0,1,a,t,(t * a ^ 2),0,0,0;
      t,0,0,0,0,0,1,0,0,t ^ 2,0,(a ^ 2 * t ^ 2);
      0,a,0,a,0,0,0,1,a ^ 2,0,0,0;
      0,0,0,0,0,0,0,0,1,0,t,(a * t);
      0,0,0,0,0,0,0,0,0,1,0,a ^ 2;
      0,0,0,0,0,0,0,0,0,0,1,a;
      0,0,0,0,0,0,0,0,0,0,0,1]

private lemma wordfalse_2_eq (t a : CoefficientField m) :
    simple_false_0 t * simple_false_1 a = wordfalse_2 t a := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [simple_false_0, simple_false_1, wordfalse_2, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private def wordfalse_3 (t a u : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,t,0,(u + (t * a ^ 2));
      0,0,1,0,0,0,0,0,a,0,0,u;
      0,0,0,1,0,0,0,0,0,0,0,0;
      u,0,0,0,1,0,a ^ 2,0,0,0,0,u ^ 2;
      0,(a * t),0,(a * t),0,1,a,t,(u + (t * a ^ 2)),0,(t * u),(a * t * u);
      t,0,0,0,0,0,1,0,0,t ^ 2,0,(a ^ 2 * t ^ 2);
      0,a,0,a,0,0,0,1,a ^ 2,0,u,(a * u);
      0,0,0,0,0,0,0,0,1,0,t,(a * t);
      0,0,0,0,0,0,0,0,0,1,0,a ^ 2;
      0,0,0,0,0,0,0,0,0,0,1,a;
      0,0,0,0,0,0,0,0,0,0,0,1]

private lemma wordfalse_3_eq (t a u : CoefficientField m) :
    wordfalse_2 t a * root_false_2 u = wordfalse_3 t a u := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [wordfalse_2, root_false_2, wordfalse_3, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private def wordfalse_4 (t a u b : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,t,0,(u + (t * a ^ 2));
      0,0,1,0,0,0,0,0,a,0,(b + (a * t)),(u + (a * b) + (t * a ^ 2));
      0,0,0,1,0,0,0,0,0,0,0,0;
      u,0,0,0,1,0,a ^ 2,0,0,(b ^ 2 + (a ^ 2 * t ^ 2)),0,(u ^ 2 + (a ^ 2 * b ^ 2) + (a ^ 4 * t ^ 2));
      (b + (a * t)),b,0,b,0,1,a,t,(u + (t * a ^ 2)),((a * t ^ 2) + (b * t)),(b ^ 2 + (t * u) + (a ^ 2 * t ^ 2)),((a * b ^ 2) + (b * u) + (b * t * a ^ 2));
      t,0,0,0,0,0,1,0,0,t ^ 2,0,b ^ 2;
      0,a,0,a,0,0,0,1,a ^ 2,(b + (a * t)),u,((a * u) + (b * a ^ 2) + (t * a ^ 3));
      0,0,0,0,0,0,0,0,1,0,t,b;
      0,0,0,0,0,0,0,0,0,1,0,a ^ 2;
      0,0,0,0,0,0,0,0,0,0,1,a;
      0,0,0,0,0,0,0,0,0,0,0,1]

private lemma wordfalse_4_eq (t a u b : CoefficientField m) :
    wordfalse_3 t a u * root_false_3 (t*a+b) = wordfalse_4 t a u b := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [wordfalse_3, root_false_3, wordfalse_4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

def cartanWord_true (t u : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,(t * (theta m t)^2 + u),0,t,0,0,0,0,0;
      0,0,1,0,(norm t u),(t * theta m t + theta m u),0,(theta m t),0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,(theta m t),1,0,0,0,0,0,0;
      0,0,0,0,(theta m t) ^ 2,0,1,0,0,0,0,0;
      0,0,0,0,(theta m u),t,0,1,0,0,0,0;
      0,(theta m t),0,(theta m t),((norm t u) * (theta m t)),u,(t * theta m t + theta m u),(theta m t) ^ 2,1,0,0,0;
      t,0,0,0,(theta m u) ^ 2,0,t ^ 2,0,0,1,0,0;
      (t * theta m t + theta m u),(theta m u),0,(theta m u),((norm t u) * (theta m u)),(titsEnd m (norm t u)),(t * (t * theta m t + theta m u)),(t * (theta m t)^2 + u),t,(theta m t),1,0;
      u,0,0,0,(norm t u) ^ 2,0,(t * theta m t + theta m u) ^ 2,0,0,(theta m t) ^ 2,0,1]

lemma cartanWord_true_eq (t u : CoefficientField m) :
    blockWord 0 true t u = cartanWord_true t u := by
  unfold blockWord
  rw [root_true_2_eq, root_true_3_eq]
  change blockSimple 0 true 0 t * blockSimple 0 true 1 (theta m t) * _ * _ = _
  rw [simple_true_0_eq, simple_true_1_eq]
  rw [wordtrue_2_eq, wordtrue_3_eq, wordtrue_4_eq]
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [cartanWord_true, wordtrue_4, tits_norm, norm, tits_theta, ← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

def cartanWord_false (t u : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,t,0,(t * (theta m t)^2 + u);
      0,0,1,0,0,0,0,0,(theta m t),0,(t * theta m t + theta m u),(norm t u);
      0,0,0,1,0,0,0,0,0,0,0,0;
      u,0,0,0,1,0,(theta m t) ^ 2,0,0,(t * theta m t + theta m u) ^ 2,0,(norm t u) ^ 2;
      (t * theta m t + theta m u),(theta m u),0,(theta m u),0,1,(theta m t),t,(t * (theta m t)^2 + u),(t * (t * theta m t + theta m u)),(titsEnd m (norm t u)),((norm t u) * (theta m u));
      t,0,0,0,0,0,1,0,0,t ^ 2,0,(theta m u) ^ 2;
      0,(theta m t),0,(theta m t),0,0,0,1,(theta m t) ^ 2,(t * theta m t + theta m u),u,((norm t u) * (theta m t));
      0,0,0,0,0,0,0,0,1,0,t,(theta m u);
      0,0,0,0,0,0,0,0,0,1,0,(theta m t) ^ 2;
      0,0,0,0,0,0,0,0,0,0,1,(theta m t);
      0,0,0,0,0,0,0,0,0,0,0,1]

lemma cartanWord_false_eq (t u : CoefficientField m) :
    blockWord 0 false t u = cartanWord_false t u := by
  unfold blockWord
  rw [root_false_2_eq, root_false_3_eq]
  change blockSimple 0 false 0 t * blockSimple 0 false 1 (theta m t) * _ * _ = _
  rw [simple_false_0_eq, simple_false_1_eq]
  rw [wordfalse_2_eq, wordfalse_3_eq, wordfalse_4_eq]
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [cartanWord_false, wordfalse_4, tits_norm, norm, tits_theta, ← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private lemma coroot_0_eq (t : CoefficientField m) (ht : t ≠ 0) :
    blockWeyl 0 0 t * blockReflection 0 0 =
      Matrix.diagonal ![1,1,1,1,1,t⁻¹ ^ 1,t⁻¹ ^ 2,t ^ 1,t⁻¹ ^ 1,t ^ 2,t ^ 1,1] := by
  rw [weyl_0_eq t ht, reflection_0_eq]
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [weyl_0, reflection_0, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]

private lemma coroot_1_eq (t : CoefficientField m) (ht : t ≠ 0) :
    blockWeyl 0 1 t * blockReflection 0 1 =
      Matrix.diagonal ![1,1,1,1,t⁻¹ ^ 2,1,t ^ 2,t⁻¹ ^ 2,t ^ 2,t⁻¹ ^ 2,1,t ^ 2] := by
  rw [weyl_1_eq t ht, reflection_1_eq]
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [weyl_1, reflection_1, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]

private def reflectionPair : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      1,1,0,0,0,0,0,0,0,0,0,0;
      0,1,1,1,0,0,0,0,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,0,0,1,0,0,0,0,0;
      0,0,0,0,0,0,0,0,1,0,0,0;
      0,0,0,0,0,0,0,0,0,0,0,1;
      0,0,0,0,0,1,0,0,0,0,0,0;
      0,0,0,0,0,0,0,0,0,0,1,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,0,0,0,1,0,0,0,0;
      0,0,0,0,0,0,0,0,0,1,0,0]

private lemma reflectionPair_eq : reflection_0 (m := m) * reflection_1 = reflectionPair := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [reflection_0, reflection_1, reflectionPair, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero, CharTwo.ofNat_eq_mod]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]

def cartanPanel : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,0,0,0;
      1,0,1,0,0,0,0,0,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,0,0,0,0,0,0,0,1;
      0,0,0,0,0,0,0,0,0,0,1,0;
      0,0,0,0,0,0,0,0,0,1,0,0;
      0,0,0,0,0,0,0,0,1,0,0,0;
      0,0,0,0,0,0,0,1,0,0,0,0;
      0,0,0,0,0,0,1,0,0,0,0,0;
      0,0,0,0,0,1,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0]

lemma cartanPanel_eq : blockPanel (R := CoefficientField m) 0 = cartanPanel := by
  rw [blockPanel, reflection_0_eq, reflection_1_eq]
  rw [mul_assoc (reflection_0 * reflection_1), reflectionPair_eq]
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [reflectionPair, cartanPanel, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero, CharTwo.ofNat_eq_mod]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]

def cartanTorus (n : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  Matrix.diagonal ![1,1,1,1,n⁻¹^2,(titsEnd m n)⁻¹,
    (titsEnd m n)⁻¹^2 * n^2,titsEnd m n * n⁻¹^2,
    (titsEnd m n)⁻¹ * n^2,(titsEnd m n)^2 * n⁻¹^2,titsEnd m n,n^2]

lemma cartanTorus_eq (n : (CoefficientField m)ˣ) :
    blockTorus 0 n = cartanTorus (n : CoefficientField m) := by
  rw [blockTorus, coroot_0_eq _ ((map_ne_zero (titsEnd m)).mpr n.ne_zero),
    coroot_1_eq _ n.ne_zero, Matrix.diagonal_mul_diagonal]
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;> simp [cartanTorus]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]


end
end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation.CartanBlock
