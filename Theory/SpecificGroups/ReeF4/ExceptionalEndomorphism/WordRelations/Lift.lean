module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Lifting a matrix intertwiner through words

An intertwining identity on invertible generators extends to their free group,
even when the intertwining matrix is singular. This is the word-level step in
the quotient-to-ideal comparison for the exceptional F4 endomorphism.
The proof uses only multiplication and inversion of the two generator matrices.
-/

public section

namespace ReeF4.WordRelations

open scoped Matrix

variable {K n : Type*} [Semiring K] [Fintype n] [DecidableEq n]

theorem intertwines_inv (T : Matrix n n K) (a b : (Matrix n n K)ˣ)
    (h : T * (a : Matrix n n K) = (b : Matrix n n K) * T) :
    T * ((a⁻¹ : (Matrix n n K)ˣ) : Matrix n n K) =
      ((b⁻¹ : (Matrix n n K)ˣ) : Matrix n n K) * T := by
  have ha : (a : Matrix n n K) * (↑a⁻¹ : Matrix n n K) = 1 := by
    simp only [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hb : (↑b⁻¹ : Matrix n n K) * (b : Matrix n n K) = 1 := by
    simp only [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc
    T * ↑a⁻¹ = (↑b⁻¹ * (b : Matrix n n K)) * (T * ↑a⁻¹) := by rw [hb, one_mul]
    _ = ↑b⁻¹ * ((b : Matrix n n K) * T) * ↑a⁻¹ := by simp only [mul_assoc]
    _ = ↑b⁻¹ * (T * (a : Matrix n n K)) * ↑a⁻¹ := by rw [h]
    _ = ↑b⁻¹ * T := by simp only [mul_assoc, ha, mul_one]

/-- A singular intertwiner is respected by arbitrary words in the generators. -/
theorem lift_intertwines {α : Type*}
    (f g : α → (Matrix n n K)ˣ) (T : Matrix n n K)
    (h : ∀ a, T * (f a : Matrix n n K) = (g a : Matrix n n K) * T)
    (w : FreeGroup α) :
    T * (FreeGroup.lift f w : Matrix n n K) =
      (FreeGroup.lift g w : Matrix n n K) * T := by
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · simp
  · intro a
    simpa using h a
  · intro a ha
    simpa only [map_inv] using intertwines_inv T
      (FreeGroup.lift f (FreeGroup.of a)) (FreeGroup.lift g (FreeGroup.of a)) ha
  · intro a b ha hb
    simp only [map_mul, Units.val_mul]
    calc
      T * (↑(FreeGroup.lift f a) * ↑(FreeGroup.lift f b)) =
          (↑(FreeGroup.lift g a) * T) * ↑(FreeGroup.lift f b) := by
            rw [← mul_assoc, ha]
      _ = (↑(FreeGroup.lift g a) * ↑(FreeGroup.lift g b)) * T := by
        rw [mul_assoc, hb, ← mul_assoc]

end ReeF4.WordRelations
