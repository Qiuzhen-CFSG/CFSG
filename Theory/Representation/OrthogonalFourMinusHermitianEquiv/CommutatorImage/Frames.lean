module

public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.CommutatorImage.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
/-!
# Transitivity on normalized singular pairs

Every singular Hermitian matrix is a column outer product. This follows by
extracting a square root of a nonzero diagonal coordinate in the fixed field;
when the first diagonal coordinate vanishes, anisotropy of the norm kills the
off-diagonal coordinate. For two singular vectors with polar pairing one,
the matrix of their columns has determinant of norm one. Multiplying the first
column by the conjugate determinant gives determinant one and preserves its
outer product. Thus SL₂ is transitive on the actual normalized singular pairs.

This is the hyperbolic-pair step in the concrete Hermitian realization of
SL₂(q²) as Omega₄⁻(q), as used in Aschbacher--Smith, I.1.6(3), printed p.408,
and F.1.12(I)(6), printed p.263. The construction includes q = 2.
-/

@[expose] public noncomputable section

namespace Representation.OrthogonalFourMinus.HermitianEquiv
open FiniteModel
open ClassicalOrthogonal.Minus (Orthogonal)
variable (n : ℕ) [NeZero n]

private theorem singular_coordinates_factor (a b : fixedField n) (z : Field n)
    (hab : a * b = FiniteModel.norm n z) :
    ∃ x y : Field n,
      (!![a.val, z; conjugation n z, b.val] : Mat (Field n)) =
        !![x * conjugation n x, x * conjugation n y;
          y * conjugation n x, y * conjugation n y] := by
  have hs : Function.Surjective (fun t : fixedField n => t ^ 2) :=
    Finite.surjective_of_injective (fun a b h => CharTwo.sq_injective h)
  by_cases ha : a = 0
  · have hz : z = 0 := (norm_eq_zero_iff n z).mp (by simpa [ha] using hab.symm)
    obtain ⟨t, ht⟩ := hs b
    have htfix : conjugation n t.val = t.val := t.property
    refine ⟨0, t.val, ?_⟩
    have ht' : t.val * t.val = b.val := by
      simpa only [pow_two, Subfield.coe_mul] using congrArg Subtype.val ht
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hz, htfix, ht']
  · obtain ⟨t, ht⟩ := hs a
    have htfix : conjugation n t.val = t.val := t.property
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht; exact ha ht.symm
    have ht0' : t.val ≠ 0 := Subtype.coe_ne_coe.mpr ht0
    have ht' : t.val * t.val = a.val := by
      simpa only [pow_two, Subfield.coe_mul] using congrArg Subtype.val ht
    have hab' : a.val * b.val = z * conjugation n z := congrArg Subtype.val hab
    refine ⟨t.val, conjugation n z / t.val, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [htfix] using ht'.symm
    · change z = t.val * conjugation n (conjugation n z / t.val)
      rw [map_div₀, conjugation_involutive, htfix]
      field_simp
    · change conjugation n z = (conjugation n z / t.val) * conjugation n t.val
      rw [htfix, div_mul_cancel₀ _ ht0']
    · change b.val = (conjugation n z / t.val) * conjugation n (conjugation n z / t.val)
      rw [map_div₀, conjugation_involutive, htfix, div_mul_div_comm]
      apply (eq_div_iff (mul_ne_zero ht0' ht0')).mpr
      calc
        b.val * (t.val * t.val) = a.val * b.val := by rw [ht']; ring
        _ = z * conjugation n z := hab'
        _ = conjugation n z * z := mul_comm _ _

/-- Singular Hermitian matrices are column outer products. -/
theorem singular_factorization (X : Space n) (hX : form n X = 0) :
    ∃ x y : Field n, X.val =
      !![x * conjugation n x, x * conjugation n y;
        y * conjugation n x, y * conjugation n y] := by
  rw [form_eq_coordinates, sub_eq_zero] at hX
  obtain ⟨x, y, hxy⟩ := singular_coordinates_factor n
    (coordinates n X).1.1 (coordinates n X).1.2 (coordinates n X).2 hX
  refine ⟨x, y, ?_⟩
  have he := congrArg Subtype.val ((coordinates n).symm_apply_apply X)
  rw [coordinates_symm_val] at he
  exact he.symm.trans hxy

/-- A normalized singular pair is obtained from the two diagonal vectors by
one determinant-one congruence. -/
theorem singular_pair_transitivity (X Y : Space n)
    (hX : form n X = 0) (hY : form n Y = 0)
    (hXY : (form n).polarBilin X Y = 1) :
    ∃ A, action n A (firstDiagonal n) = X ∧ action n A (secondDiagonal n) = Y := by
  obtain ⟨x, y, hv⟩ := singular_factorization n X hX
  obtain ⟨z, w, hw⟩ := singular_factorization n Y hY
  let d := x * w - z * y
  have hd : d * conjugation n d = 1 := by
    have hsum : form n (X + Y) = 1 := by
      simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
        hX, hY, sub_zero] using hXY
    have hdet : (X.val + Y.val).det = 1 := congrArg Subtype.val hsum
    calc
      d * conjugation n d = (X.val + Y.val).det := by
        rw [hv, hw]
        simp [d, Matrix.det_fin_two, map_sub, map_mul]
        ring
      _ = 1 := hdet
  have hdc : conjugation n d * d = 1 := by rw [mul_comm]; exact hd
  let A : Matrix.SpecialLinearGroup (Fin 2) (Field n) :=
    ⟨!![conjugation n d * x, z; conjugation n d * y, w], by
      rw [Matrix.det_fin_two]
      calc
        conjugation n d * x * w - z * (conjugation n d * y) =
          conjugation n d * d := by dsimp [d]; ring
        _ = 1 := hdc⟩
  have hscale (a b : Field n) :
      (conjugation n d * a) * conjugation n (conjugation n d * b) =
        a * conjugation n b := by
    rw [map_mul, conjugation_involutive]
    calc
      (conjugation n d * a) * (d * conjugation n b) =
          (conjugation n d * d) * (a * conjugation n b) := by ring
      _ = a * conjugation n b := by rw [hdc, one_mul]
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
    (g : Orthogonal (fixedField n) (Space n) (form n)) :
    ∃ A, (orthogonalAction n A).val (firstDiagonal n) = g.val (firstDiagonal n) ∧
      (orthogonalAction n A).val (secondDiagonal n) = g.val (secondDiagonal n) := by
  have hg := (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp g.property
  apply singular_pair_transitivity n
  · rw [hg]
    change form n ((coordinates n).symm ((1, 0), 0)) = 0
    rw [form_coordinates]
    apply Subtype.ext
    simp [FiniteModel.norm]
  · rw [hg]
    change form n ((coordinates n).symm ((0, 1), 0)) = 0
    rw [form_coordinates]
    apply Subtype.ext
    simp [FiniteModel.norm]
  · rw [polar_preserved]
    apply Subtype.ext
    rw [coe_polar_coordinates]
    simp [firstDiagonal, secondDiagonal]

end Representation.OrthogonalFourMinus.HermitianEquiv
