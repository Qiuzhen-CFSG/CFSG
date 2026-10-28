module
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.CommutatorImage.Basic
/-!
# Transitivity on Hermitian singular pairs

Surjectivity of the finite-field norm factors every singular Hermitian matrix
as a column outer product. For two such matrices with polar pairing one,
the matrix of their columns has determinant of norm one. Scaling the first
column by the conjugate determinant preserves its outer product and makes
the determinant one. Hence the actual SL₂ congruences move the standard
diagonal pair to the image of that pair under every full isometry.

This is the frame step in the minus-four comparison used in
Aschbacher–Smith A.2.17, printed pp.38–39 (`refs/quasithin.pdf`), with the
orthogonal conventions of GLS3 §2.7. The construction adapts
`Representation.OrthogonalFourMinus.HermitianEquiv.CommutatorImage.Frames`,
replacing its characteristic-two square roots by field norms.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
open Representation.OrthogonalFourMinus
universe u
variable {E : Type u} [Field E] (σ : E ≃+* E) (hσ : Function.Involutive σ)
variable [Finite E] (hdegree : Module.finrank (fixedField σ) E = 2)
    (hne : ∃ t : E, σ t ≠ t)
include hdegree hne

private theorem singular_coordinates_factor (a b : fixedField σ) (z : E)
    (hab : a * b = norm σ hσ z) :
    ∃ x y : E,
      (!![a.val, z; σ z, b.val] : Mat E) =
        !![x * σ x, x * σ y;
          y * σ x, y * σ y] := by
  have hs := norm_surjective σ hσ hdegree hne
  by_cases ha : a = 0
  · have hz : z = 0 := (norm_eq_zero_iff σ hσ z).mp (by simpa [ha] using hab.symm)
    obtain ⟨t, ht⟩ := hs b
    refine ⟨0, t, ?_⟩
    have ht' : t * σ t = b.val := congrArg Subtype.val ht
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hz, ht']
  · obtain ⟨t, ht⟩ := hs a
    have ht0 : t ≠ 0 := by
      intro h
      apply ha
      rw [← ht, h]
      exact (norm_eq_zero_iff σ hσ 0).mpr rfl
    have ht0' : σ t ≠ 0 := (map_ne_zero σ).mpr ht0
    have ht' : t * σ t = a.val := congrArg Subtype.val ht
    have hab' : a.val * b.val = z * σ z := congrArg Subtype.val hab
    refine ⟨t, σ z / σ t, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · exact ht'.symm
    · change z = t * σ (σ z / σ t)
      rw [map_div₀, hσ, hσ]
      field_simp
    · change σ z = (σ z / σ t) * σ t
      rw [div_mul_cancel₀ _ ht0']
    · change b.val = (σ z / σ t) * σ (σ z / σ t)
      rw [map_div₀, hσ, hσ, div_mul_div_comm]
      apply (eq_div_iff (mul_ne_zero ht0' ht0)).mpr
      calc
        b.val * (σ t * t) = a.val * b.val := by rw [mul_comm (σ t), ht']; ring
        _ = z * σ z := hab'
        _ = σ z * z := mul_comm _ _

/-- Singular Hermitian matrices are column outer products. -/
theorem singular_factorization (X : Space σ hσ) (hX : form σ hσ X = 0) :
    ∃ x y : E, X.val =
      !![x * σ x, x * σ y;
        y * σ x, y * σ y] := by
  rw [form_eq_coordinates, sub_eq_zero] at hX
  obtain ⟨x, y, hxy⟩ := singular_coordinates_factor σ hσ hdegree hne
    (coordinates σ hσ X).1.1 (coordinates σ hσ X).1.2 (coordinates σ hσ X).2 hX
  refine ⟨x, y, ?_⟩
  have he := congrArg Subtype.val ((coordinates σ hσ).symm_apply_apply X)
  rw [coordinates_symm_val] at he
  exact he.symm.trans hxy

/-- A normalized singular pair is obtained from the two diagonal vectors by
one determinant-one congruence. -/
theorem singular_pair_transitivity (X Y : Space σ hσ)
    (hX : form σ hσ X = 0) (hY : form σ hσ Y = 0)
    (hXY : (form σ hσ).polarBilin X Y = 1) :
    ∃ A, action σ hσ A (firstDiagonal σ hσ) = X ∧ action σ hσ A (secondDiagonal σ hσ) = Y := by
  obtain ⟨x, y, hv⟩ := singular_factorization σ hσ hdegree hne X hX
  obtain ⟨z, w, hw⟩ := singular_factorization σ hσ hdegree hne Y hY
  let d := x * w - z * y
  have hd : d * σ d = 1 := by
    have hsum : form σ hσ (X + Y) = 1 := by
      simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
        hX, hY, sub_zero] using hXY
    have hdet : (X.val + Y.val).det = 1 := congrArg Subtype.val hsum
    calc
      d * σ d = (X.val + Y.val).det := by
        rw [hv, hw]
        simp [d, Matrix.det_fin_two, map_sub, map_mul]
        ring
      _ = 1 := hdet
  have hdc : σ d * d = 1 := by rw [mul_comm]; exact hd
  let A : Matrix.SpecialLinearGroup (Fin 2) (E) :=
    ⟨!![σ d * x, z; σ d * y, w], by
      rw [Matrix.det_fin_two]
      calc
        σ d * x * w - z * (σ d * y) =
          σ d * d := by dsimp [d]; ring
        _ = 1 := hdc⟩
  have hscale (a b : E) :
      (σ d * a) * σ (σ d * b) =
        a * σ b := by
    rw [map_mul, hσ]
    calc
      (σ d * a) * (d * σ b) =
          (σ d * d) * (a * σ b) := by ring
      _ = a * σ b := by rw [hdc, one_mul]
  refine ⟨A, ?_, ?_⟩
  · apply Subtype.ext
    rw [action_apply, hv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simpa [A, firstDiagonal, coordinates_symm_val, adjoint,
        Matrix.mul_apply, Fin.sum_univ_two] using hscale _ _
  · apply Subtype.ext
    rw [action_apply, hw]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, secondDiagonal, coordinates_symm_val, adjoint,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- Every full isometry's diagonal pair has an SL₂ congruence with the same images. -/
theorem orthogonal_diagonal_pair_transitivity
    (g : Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ)) :
    ∃ A, (orthogonalAction σ hσ A).val (firstDiagonal σ hσ) = g.val (firstDiagonal σ hσ) ∧
      (orthogonalAction σ hσ A).val (secondDiagonal σ hσ) = g.val (secondDiagonal σ hσ) := by
  have hg := form_preserved_of_orthogonal σ hσ g
  apply singular_pair_transitivity σ hσ hdegree hne
  · rw [hg]
    change form σ hσ ((coordinates σ hσ).symm ((1, 0), 0)) = 0
    rw [form_coordinates]
    apply Subtype.ext
    simp [norm]
  · rw [hg]
    change form σ hσ ((coordinates σ hσ).symm ((0, 1), 0)) = 0
    rw [form_coordinates]
    apply Subtype.ext
    simp [norm]
  · rw [polar_preserved]
    apply Subtype.ext
    rw [coe_polar_coordinates]
    simp [firstDiagonal, secondDiagonal]


end ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
