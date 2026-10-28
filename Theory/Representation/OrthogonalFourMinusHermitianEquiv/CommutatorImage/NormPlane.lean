module

public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.CommutatorImage.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push

/-!
# The pointwise stabilizer of a Hermitian hyperbolic pair

The two diagonal vectors detect the diagonal coordinates through the polar
form. An isometry fixing them therefore restricts to an additive norm isometry
of the off-diagonal quadratic extension. Dividing by its value at one gives
a map fixing one; preservation of norm then gives preservation of trace, so
each element maps either to itself or to its conjugate. Additivity makes this
choice uniform. A norm-one square root realizes the remaining scalar by an
actual determinant-one diagonal congruence, including over GF(4).

The result classifies the literal pointwise stabilizer used in the Hermitian
SL₂--Omega identification of Aschbacher--Smith, I.1.6(3), printed p.408.
-/

@[expose] public noncomputable section

namespace Representation.OrthogonalFourMinus.HermitianEquiv
open FiniteModel
variable (n : ℕ) [NeZero n]

omit [NeZero n] in
private theorem norm_preserving_fixed_one (T : Field n →+ Field n)
    (h1 : T 1 = 1)
    (hN : ∀ z, T z * conjugation n (T z) = z * conjugation n z) :
    (∀ z, T z = z) ∨ (∀ z, T z = conjugation n z) := by
  have htrace (z : Field n) : T z + conjugation n (T z) = z + conjugation n z := by
    have h := hN (z + 1)
    simp only [map_add, h1, map_one] at h
    linear_combination h - hN z
  have heither (z : Field n) : T z = z ∨ T z = conjugation n z := by
    have hp : (T z - z) * (T z - conjugation n z) = 0 := by
      linear_combination T z * htrace z - hN z
    simpa only [mul_eq_zero, sub_eq_zero] using hp
  by_cases h : ∀ z, T z = z
  · exact Or.inl h
  · push Not at h
    obtain ⟨t, ht⟩ := h
    have htt := (heither t).resolve_left ht
    right
    intro z
    rcases heither z with hz | hz
    · rcases heither (t + z) with htz | htz
      · rw [map_add, hz] at htz
        exact (ht (add_right_cancel htz)).elim
      · rw [map_add, htt, hz, map_add] at htz
        exact hz.trans (add_left_cancel htz)
    · exact hz

/-- An additive norm isometry is multiplication by a norm-one element,
possibly followed by conjugation. -/
theorem norm_isometry_normal_form (L : Field n →+ Field n)
    (hN : ∀ z, FiniteModel.norm n (L z) = FiniteModel.norm n z) :
    ∃ u : Field n, FiniteModel.norm n u = 1 ∧
      ((∀ z, L z = u * z) ∨ (∀ z, L z = u * conjugation n z)) := by
  have hN' (z : Field n) : L z * conjugation n (L z) = z * conjugation n z :=
    congrArg Subtype.val (hN z)
  let u := L 1
  have hu : u * conjugation n u = 1 := by simpa [u] using hN' 1
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  let T : Field n →+ Field n :=
    { toFun := fun z => u⁻¹ * L z
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add] }
  have hT1 : T 1 = 1 := by exact inv_mul_cancel₀ hu0
  have hTN (z : Field n) : T z * conjugation n (T z) = z * conjugation n z := by
    change (u⁻¹ * L z) * conjugation n (u⁻¹ * L z) = _
    rw [map_mul, map_inv₀]
    calc
      (u⁻¹ * L z) * ((conjugation n u)⁻¹ * conjugation n (L z)) =
          (u * conjugation n u)⁻¹ * (L z * conjugation n (L z)) := by
            rw [mul_inv]; ring
      _ = z * conjugation n z := by rw [hu, hN']; simp
  refine ⟨u, ?_, ?_⟩
  · apply Subtype.ext
    exact hu
  · rcases norm_preserving_fixed_one n T hT1 hTN with h | h
    · left
      intro z
      have he := congrArg (u * ·) (h z)
      simpa [T, ← mul_assoc, hu0] using he
    · right
      intro z
      have he := congrArg (u * ·) (h z)
      simpa [T, ← mul_assoc, hu0] using he

open ClassicalOrthogonal.Minus (Orthogonal)

/-- A full determinant isometry fixing the diagonal vectors restricts to a norm isometry. -/
theorem stabilizer_offDiagonal
    (g : Orthogonal (fixedField n) (Space n) (form n))
    (h0 : g.val (firstDiagonal n) = firstDiagonal n)
    (h1 : g.val (secondDiagonal n) = secondDiagonal n) :
    ∃ u : Field n, FiniteModel.norm n u = 1 ∧
      ((∀ z, g.val (offDiagonal n z) = offDiagonal n (u * z)) ∨
        (∀ z, g.val (offDiagonal n z) = offDiagonal n (u * conjugation n z))) := by
  have ha (z : Field n) : (coordinates n (g.val (offDiagonal n z))).1.1 = 0 := by
    have h := congrArg Subtype.val (polar_preserved n g (secondDiagonal n) (offDiagonal n z))
    rw [h1, coe_polar_coordinates, coe_polar_coordinates] at h
    apply Subtype.ext
    simpa [secondDiagonal] using h
  have hb (z : Field n) : (coordinates n (g.val (offDiagonal n z))).1.2 = 0 := by
    have h := congrArg Subtype.val (polar_preserved n g (firstDiagonal n) (offDiagonal n z))
    rw [h0, coe_polar_coordinates, coe_polar_coordinates] at h
    apply Subtype.ext
    simpa [firstDiagonal] using h
  let L : Field n →ₗ[fixedField n] Field n :=
    { toFun := fun z => (coordinates n (g.val (offDiagonal n z))).2
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  have hgL (z : Field n) : g.val (offDiagonal n z) = offDiagonal n (L z) := by
    apply (coordinates n).injective
    rw [coordinates_offDiagonal]
    exact Prod.ext (Prod.ext (ha z) (hb z)) rfl
  have hN (z : Field n) : FiniteModel.norm n (L z) = FiniteModel.norm n z := by
    have h := (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp g.property
      (offDiagonal n z)
    rw [hgL] at h
    change form n ((coordinates n).symm ((0, 0), L z)) =
      form n ((coordinates n).symm ((0, 0), z)) at h
    rw [form_coordinates, form_coordinates] at h
    simpa only [zero_mul, zero_sub, neg_inj] using h
  obtain ⟨u, hu, h | h⟩ := norm_isometry_normal_form n L.toAddMonoidHom hN
  · exact ⟨u, hu, Or.inl (fun z => (hgL z).trans (congrArg (offDiagonal n) (h z)))⟩
  · exact ⟨u, hu, Or.inr (fun z => (hgL z).trans (congrArg (offDiagonal n) (h z)))⟩

/-- In characteristic two a norm-one element has a norm-one square root. -/
theorem norm_one_square_root (u : Field n) (hu : FiniteModel.norm n u = 1) :
    ∃ t : Field n, t ≠ 0 ∧ t ^ 2 = u ∧ t * conjugation n t = 1 := by
  have hs : Function.Surjective (fun t : Field n => t ^ 2) :=
    Finite.surjective_of_injective (fun a b h => CharTwo.sq_injective h)
  obtain ⟨t, ht⟩ := hs u
  have hN : t * conjugation n t = 1 := by
    have h : u * conjugation n u = 1 := congrArg Subtype.val hu
    rw [← ht, map_pow, ← mul_pow] at h
    exact CharTwo.sq_injective (by simpa only [one_pow] using h)
  refine ⟨t, ?_, ht, hN⟩
  intro h
  simp [h] at hN

/-- Norm-one diagonal congruences act on the norm plane by their square. -/
theorem coordinates_diagonal_action (t : Field n) (ht : t ≠ 0)
    (hN : t * conjugation n t = 1) (X : Space n) :
    coordinates n (action n (Matrix.SpecialLinearGroup.diag2 t ht) X) =
      ((coordinates n X).1, t ^ 2 * (coordinates n X).2) := by
  have hc : conjugation n t = t⁻¹ := eq_inv_of_mul_eq_one_right hN
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · simp [coordinates, action_apply, Matrix.SpecialLinearGroup.diag2_coe',
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, adjoint, hc]
      field_simp
    · simp [coordinates, action_apply, Matrix.SpecialLinearGroup.diag2_coe',
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, adjoint, hc]
      field_simp
  · simp [coordinates, action_apply, Matrix.SpecialLinearGroup.diag2_coe',
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, adjoint, hc]
    ring

@[simp] theorem coordinates_conjugation (X : Space n) :
    coordinates n ((conjugationOrthogonal n).val X) =
      ((coordinates n X).1, conjugation n (coordinates n X).2) := by
  apply Prod.ext
  · rfl
  · exact (entry_conjugate n X 1 0).symm

private theorem diagonal_decomposition (X : Space n) :
    X = (coordinates n X).1.1 • firstDiagonal n +
      (coordinates n X).1.2 • secondDiagonal n + offDiagonal n (coordinates n X).2 := by
  apply (coordinates n).injective
  simp [firstDiagonal, secondDiagonal, Prod.ext_iff]

/-- The pointwise stabilizer of the diagonal hyperbolic pair is generated by
norm-one diagonal congruences and conjugation. -/
theorem diagonal_stabilizer_normal_form
    (g : Orthogonal (fixedField n) (Space n) (form n))
    (h0 : g.val (firstDiagonal n) = firstDiagonal n)
    (h1 : g.val (secondDiagonal n) = secondDiagonal n) :
    ∃ A, g = orthogonalAction n A ∨
      g = orthogonalAction n A * conjugationOrthogonal n := by
  have hcoord (f : Field n → Field n)
      (hf : ∀ z, g.val (offDiagonal n z) = offDiagonal n (f z)) (X : Space n) :
      coordinates n (g.val X) = ((coordinates n X).1, f (coordinates n X).2) := by
    calc
      coordinates n (g.val X) = coordinates n (g.val
          ((coordinates n X).1.1 • firstDiagonal n +
            (coordinates n X).1.2 • secondDiagonal n + offDiagonal n (coordinates n X).2)) :=
        congrArg (fun Y => coordinates n (g.val Y)) (diagonal_decomposition n X)
      _ = _ := by
        simp only [map_add, map_smul, h0, h1, hf]
        simp [firstDiagonal, secondDiagonal, Prod.ext_iff]
  obtain ⟨u, hu, h⟩ := stabilizer_offDiagonal n g h0 h1
  obtain ⟨t, ht0, ht2, htN⟩ := norm_one_square_root n u hu
  refine ⟨Matrix.SpecialLinearGroup.diag2 t ht0, ?_⟩
  rcases h with h | h
  · left
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    apply (coordinates n).injective
    change coordinates n (g.val X) =
      coordinates n (action n (Matrix.SpecialLinearGroup.diag2 t ht0) X)
    rw [coordinates_diagonal_action n t ht0 htN, ht2]
    exact hcoord (fun z => u * z) h X
  · right
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    apply (coordinates n).injective
    change coordinates n (g.val X) =
      coordinates n (action n (Matrix.SpecialLinearGroup.diag2 t ht0)
        ((conjugationOrthogonal n).val X))
    rw [coordinates_diagonal_action n t ht0 htN, ht2, coordinates_conjugation]
    exact hcoord (fun z => u * conjugation n z) h X

end Representation.OrthogonalFourMinus.HermitianEquiv
