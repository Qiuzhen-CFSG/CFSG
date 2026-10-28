module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation.Blocks
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation.CartanBlock.Words
/-!
# The complete Gauss equation on the twelve-dimensional Cartan block

The explicit word, Weyl, and torus comparisons preserve all four Cartan
coordinates and the eight root coordinates [24,25,26,27,28,29,30,31].
The panel contains a Cartan shear in entry (2,0), so checking the root
coordinates alone would not establish this equation.

After substituting the negative and positive Gauss parameters, the reciprocal
norm identities and the theta identities reduce each row to field arithmetic.
We expand the diagonal product entrywise and clear only the nonzero norm and
its Tits image. The twelve row proofs cover every entry; their assembly gives
`blockGauss_cartan` without an additional hypothesis.

Source: GLS3, Table 2.4 type V, 2.3.4--8 and 2.6.5,
`refs/KGroup/GLS3/chapter2.tex`; the checked scalar identities in
`Gauss.Coordinates` and the full coefficient supports in `Ambient.Tables`.
-/

namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation.CartanBlock
open BlockParameters.FieldRecovery
open scoped Matrix
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {m : ℕ}
private lemma diagonal_product_entry
    (A B : Matrix (Fin 12) (Fin 12) (CoefficientField m))
    (d : Fin 12 → CoefficientField m) (r c : Fin 12) :
    (A * Matrix.diagonal d * B) r c = ∑ k, A r k * d k * B k c := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]

private lemma positive_linear (t u : CoefficientField m) :
    positiveFirst t u * (theta m (positiveFirst t u))^2 + positiveSecond t u =
      negativeSecond t u := by
  rw [theta_sq, positiveSecond]
  simp [add_assoc, add_left_comm, add_comm, CharTwo.add_self_eq_zero]

private lemma cartanGauss_row0 (t u : CoefficientField m) (hn : norm t u ≠ 0)
    (c : Fin 12) :
    (cartanPanel (m := m) * cartanWord_false t u) 0 c =
      (cartanWord_false (negativeFirst t u) (negativeSecond t u) *
        cartanTorus (norm t u) *
          cartanWord_true (positiveFirst t u) (positiveSecond t u)) 0 c := by
  simp only [cartanTorus]
  rw [diagonal_product_entry, Matrix.mul_apply]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [cartanWord_false, cartanWord_true, positive_linear, norm_negative t u hn,
    norm_positive t u hn, theta_negativeFirst, theta_negativeSecond,
    theta_positiveFirst, theta_positiveSecond, map_inv₀]
  dsimp only [positiveFirst, negativeFirst, negativeSecond]
  fin_cases c <;>
    simp [cartanPanel, cartanTorus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [positiveSecond, positiveFirst, negativeFirst, negativeSecond,
    map_div₀, map_add, map_mul, map_pow, titsEnd_twice, tits_theta]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private lemma cartanGauss_row1 (t u : CoefficientField m) (hn : norm t u ≠ 0)
    (c : Fin 12) :
    (cartanPanel (m := m) * cartanWord_false t u) 1 c =
      (cartanWord_false (negativeFirst t u) (negativeSecond t u) *
        cartanTorus (norm t u) *
          cartanWord_true (positiveFirst t u) (positiveSecond t u)) 1 c := by
  simp only [cartanTorus]
  rw [diagonal_product_entry, Matrix.mul_apply]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [cartanWord_false, cartanWord_true, positive_linear, norm_negative t u hn,
    norm_positive t u hn, theta_negativeFirst, theta_negativeSecond,
    theta_positiveFirst, theta_positiveSecond, map_inv₀]
  dsimp only [positiveFirst, negativeFirst, negativeSecond]
  fin_cases c <;>
    simp [cartanPanel, cartanTorus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [positiveSecond, positiveFirst, negativeFirst, negativeSecond,
    map_div₀, map_add, map_mul, map_pow, titsEnd_twice, tits_theta]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private lemma cartanGauss_row2 (t u : CoefficientField m) (hn : norm t u ≠ 0)
    (c : Fin 12) :
    (cartanPanel (m := m) * cartanWord_false t u) 2 c =
      (cartanWord_false (negativeFirst t u) (negativeSecond t u) *
        cartanTorus (norm t u) *
          cartanWord_true (positiveFirst t u) (positiveSecond t u)) 2 c := by
  simp only [cartanTorus]
  rw [diagonal_product_entry, Matrix.mul_apply]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [cartanWord_false, cartanWord_true, positive_linear, norm_negative t u hn,
    norm_positive t u hn, theta_negativeFirst, theta_negativeSecond,
    theta_positiveFirst, theta_positiveSecond, map_inv₀]
  dsimp only [positiveFirst, negativeFirst, negativeSecond]
  fin_cases c <;>
    simp [cartanPanel, cartanTorus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [positiveSecond, positiveFirst, negativeFirst, negativeSecond,
    map_div₀, map_add, map_mul, map_pow, titsEnd_twice, tits_theta]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private lemma cartanGauss_row3 (t u : CoefficientField m) (hn : norm t u ≠ 0)
    (c : Fin 12) :
    (cartanPanel (m := m) * cartanWord_false t u) 3 c =
      (cartanWord_false (negativeFirst t u) (negativeSecond t u) *
        cartanTorus (norm t u) *
          cartanWord_true (positiveFirst t u) (positiveSecond t u)) 3 c := by
  simp only [cartanTorus]
  rw [diagonal_product_entry, Matrix.mul_apply]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [cartanWord_false, cartanWord_true, positive_linear, norm_negative t u hn,
    norm_positive t u hn, theta_negativeFirst, theta_negativeSecond,
    theta_positiveFirst, theta_positiveSecond, map_inv₀]
  dsimp only [positiveFirst, negativeFirst, negativeSecond]
  fin_cases c <;>
    simp [cartanPanel, cartanTorus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [positiveSecond, positiveFirst, negativeFirst, negativeSecond,
    map_div₀, map_add, map_mul, map_pow, titsEnd_twice, tits_theta]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private lemma cartanGauss_row4 (t u : CoefficientField m) (hn : norm t u ≠ 0)
    (c : Fin 12) :
    (cartanPanel (m := m) * cartanWord_false t u) 4 c =
      (cartanWord_false (negativeFirst t u) (negativeSecond t u) *
        cartanTorus (norm t u) *
          cartanWord_true (positiveFirst t u) (positiveSecond t u)) 4 c := by
  simp only [cartanTorus]
  rw [diagonal_product_entry, Matrix.mul_apply]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [cartanWord_false, cartanWord_true, positive_linear, norm_negative t u hn,
    norm_positive t u hn, theta_negativeFirst, theta_negativeSecond,
    theta_positiveFirst, theta_positiveSecond, map_inv₀]
  dsimp only [positiveFirst, negativeFirst, negativeSecond]
  fin_cases c <;>
    simp [cartanPanel, cartanTorus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [positiveSecond, positiveFirst, negativeFirst, negativeSecond,
    map_div₀, map_add, map_mul, map_pow, titsEnd_twice, tits_theta]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private lemma cartanGauss_row5 (t u : CoefficientField m) (hn : norm t u ≠ 0)
    (c : Fin 12) :
    (cartanPanel (m := m) * cartanWord_false t u) 5 c =
      (cartanWord_false (negativeFirst t u) (negativeSecond t u) *
        cartanTorus (norm t u) *
          cartanWord_true (positiveFirst t u) (positiveSecond t u)) 5 c := by
  simp only [cartanTorus]
  rw [diagonal_product_entry, Matrix.mul_apply]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [cartanWord_false, cartanWord_true, positive_linear, norm_negative t u hn,
    norm_positive t u hn, theta_negativeFirst, theta_negativeSecond,
    theta_positiveFirst, theta_positiveSecond, map_inv₀]
  dsimp only [positiveFirst, negativeFirst, negativeSecond]
  fin_cases c <;>
    simp [cartanPanel, cartanTorus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [positiveSecond, positiveFirst, negativeFirst, negativeSecond,
    map_div₀, map_add, map_mul, map_pow, titsEnd_twice, tits_theta]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private lemma cartanGauss_row6 (t u : CoefficientField m) (hn : norm t u ≠ 0)
    (c : Fin 12) :
    (cartanPanel (m := m) * cartanWord_false t u) 6 c =
      (cartanWord_false (negativeFirst t u) (negativeSecond t u) *
        cartanTorus (norm t u) *
          cartanWord_true (positiveFirst t u) (positiveSecond t u)) 6 c := by
  simp only [cartanTorus]
  rw [diagonal_product_entry, Matrix.mul_apply]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [cartanWord_false, cartanWord_true, positive_linear, norm_negative t u hn,
    norm_positive t u hn, theta_negativeFirst, theta_negativeSecond,
    theta_positiveFirst, theta_positiveSecond, map_inv₀]
  dsimp only [positiveFirst, negativeFirst, negativeSecond]
  fin_cases c <;>
    simp [cartanPanel, cartanTorus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [positiveSecond, positiveFirst, negativeFirst, negativeSecond,
    map_div₀, map_add, map_mul, map_pow, titsEnd_twice, tits_theta]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private lemma cartanGauss_row7 (t u : CoefficientField m) (hn : norm t u ≠ 0)
    (c : Fin 12) :
    (cartanPanel (m := m) * cartanWord_false t u) 7 c =
      (cartanWord_false (negativeFirst t u) (negativeSecond t u) *
        cartanTorus (norm t u) *
          cartanWord_true (positiveFirst t u) (positiveSecond t u)) 7 c := by
  simp only [cartanTorus]
  rw [diagonal_product_entry, Matrix.mul_apply]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [cartanWord_false, cartanWord_true, positive_linear, norm_negative t u hn,
    norm_positive t u hn, theta_negativeFirst, theta_negativeSecond,
    theta_positiveFirst, theta_positiveSecond, map_inv₀]
  dsimp only [positiveFirst, negativeFirst, negativeSecond]
  fin_cases c <;>
    simp [cartanPanel, cartanTorus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [positiveSecond, positiveFirst, negativeFirst, negativeSecond,
    map_div₀, map_add, map_mul, map_pow, titsEnd_twice, tits_theta]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private lemma cartanGauss_row8 (t u : CoefficientField m) (hn : norm t u ≠ 0)
    (c : Fin 12) :
    (cartanPanel (m := m) * cartanWord_false t u) 8 c =
      (cartanWord_false (negativeFirst t u) (negativeSecond t u) *
        cartanTorus (norm t u) *
          cartanWord_true (positiveFirst t u) (positiveSecond t u)) 8 c := by
  simp only [cartanTorus]
  rw [diagonal_product_entry, Matrix.mul_apply]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [cartanWord_false, cartanWord_true, positive_linear, norm_negative t u hn,
    norm_positive t u hn, theta_negativeFirst, theta_negativeSecond,
    theta_positiveFirst, theta_positiveSecond, map_inv₀]
  dsimp only [positiveFirst, negativeFirst, negativeSecond]
  fin_cases c <;>
    simp [cartanPanel, cartanTorus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [positiveSecond, positiveFirst, negativeFirst, negativeSecond,
    map_div₀, map_add, map_mul, map_pow, titsEnd_twice, tits_theta]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private lemma cartanGauss_row9 (t u : CoefficientField m) (hn : norm t u ≠ 0)
    (c : Fin 12) :
    (cartanPanel (m := m) * cartanWord_false t u) 9 c =
      (cartanWord_false (negativeFirst t u) (negativeSecond t u) *
        cartanTorus (norm t u) *
          cartanWord_true (positiveFirst t u) (positiveSecond t u)) 9 c := by
  simp only [cartanTorus]
  rw [diagonal_product_entry, Matrix.mul_apply]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [cartanWord_false, cartanWord_true, positive_linear, norm_negative t u hn,
    norm_positive t u hn, theta_negativeFirst, theta_negativeSecond,
    theta_positiveFirst, theta_positiveSecond, map_inv₀]
  dsimp only [positiveFirst, negativeFirst, negativeSecond]
  fin_cases c <;>
    simp [cartanPanel, cartanTorus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [positiveSecond, positiveFirst, negativeFirst, negativeSecond,
    map_div₀, map_add, map_mul, map_pow, titsEnd_twice, tits_theta]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private lemma cartanGauss_row10 (t u : CoefficientField m) (hn : norm t u ≠ 0)
    (c : Fin 12) :
    (cartanPanel (m := m) * cartanWord_false t u) 10 c =
      (cartanWord_false (negativeFirst t u) (negativeSecond t u) *
        cartanTorus (norm t u) *
          cartanWord_true (positiveFirst t u) (positiveSecond t u)) 10 c := by
  simp only [cartanTorus]
  rw [diagonal_product_entry, Matrix.mul_apply]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [cartanWord_false, cartanWord_true, positive_linear, norm_negative t u hn,
    norm_positive t u hn, theta_negativeFirst, theta_negativeSecond,
    theta_positiveFirst, theta_positiveSecond, map_inv₀]
  dsimp only [positiveFirst, negativeFirst, negativeSecond]
  fin_cases c <;>
    simp [cartanPanel, cartanTorus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [positiveSecond, positiveFirst, negativeFirst, negativeSecond,
    map_div₀, map_add, map_mul, map_pow, titsEnd_twice, tits_theta]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

private lemma cartanGauss_row11 (t u : CoefficientField m) (hn : norm t u ≠ 0)
    (c : Fin 12) :
    (cartanPanel (m := m) * cartanWord_false t u) 11 c =
      (cartanWord_false (negativeFirst t u) (negativeSecond t u) *
        cartanTorus (norm t u) *
          cartanWord_true (positiveFirst t u) (positiveSecond t u)) 11 c := by
  simp only [cartanTorus]
  rw [diagonal_product_entry, Matrix.mul_apply]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [cartanWord_false, cartanWord_true, positive_linear, norm_negative t u hn,
    norm_positive t u hn, theta_negativeFirst, theta_negativeSecond,
    theta_positiveFirst, theta_positiveSecond, map_inv₀]
  dsimp only [positiveFirst, negativeFirst, negativeSecond]
  fin_cases c <;>
    simp [cartanPanel, cartanTorus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [positiveSecond, positiveFirst, negativeFirst, negativeSecond,
    map_div₀, map_add, map_mul, map_pow, titsEnd_twice, tits_theta]
  all_goals try field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals try simp [CharTwo.ofNat_eq_mod]

end
end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation.CartanBlock
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation
open CartanBlock
noncomputable section
/-- The Suzuki Gauss factorization on all twelve Cartan-block coordinates. -/
public theorem blockGauss_cartan (m : ℕ) : BlockGauss m 0 := by
  intro t u hn
  rw [cartanPanel_eq, cartanWord_false_eq, cartanWord_false_eq,
    cartanTorus_eq, cartanWord_true_eq]
  dsimp +instances only [blockSize, Matrix.cons_val_zero, Units.val_mk0]
  ext r c
  fin_cases r
  · exact cartanGauss_row0 t u hn c
  · exact cartanGauss_row1 t u hn c
  · exact cartanGauss_row2 t u hn c
  · exact cartanGauss_row3 t u hn c
  · exact cartanGauss_row4 t u hn c
  · exact cartanGauss_row5 t u hn c
  · exact cartanGauss_row6 t u hn c
  · exact cartanGauss_row7 t u hn c
  · exact cartanGauss_row8 t u hn c
  · exact cartanGauss_row9 t u hn c
  · exact cartanGauss_row10 t u hn c
  · exact cartanGauss_row11 t u hn c

end
end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation
