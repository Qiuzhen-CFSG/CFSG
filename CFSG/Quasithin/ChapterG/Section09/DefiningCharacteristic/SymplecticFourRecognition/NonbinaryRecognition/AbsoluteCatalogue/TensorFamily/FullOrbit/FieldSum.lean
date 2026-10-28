module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Two
/-!
# The finite-field coefficient of the full symplectic tensor orbit sum

For the upper symplectic matrices parametrized by `(b,x,y,z)`, the two
basic highest-to-lowest entries are `x` and `x*z+y^2+b*y*z`.
Summing first in `b` gives zero when `y*z=0`, and one otherwise.
The remaining three sums of `(q-1)`st powers are each one in characteristic two.

This is the explicit norm calculation for the tensor of all basic factors
in GLS3, 2.8.6(a), 2.8.10(d), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
open scoped BigOperators
open Finset
set_option linter.unusedSimpArgs false
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.FullOrbit
variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [DecidableEq F]
lemma power_sum : ∑ x : F, x ^ (Fintype.card F - 1) = (1 : F) := by
  classical
  have hq : Fintype.card F - 1 ≠ 0 := by have := Fintype.one_lt_card (α := F); omega
  have hp (x : F) : x ^ (Fintype.card F - 1) = if x = 0 then 0 else 1 := by
    split_ifs with hx
    · simp [hx, hq]
    · exact FiniteField.pow_card_sub_one_eq_one _ hx
  simp_rw [hp]
  simp [sum_ite, filter_ne', card_erase_of_mem, Nat.cast_sub Fintype.card_pos,
    CharTwo.neg_eq]
lemma affine_sum (a b : F) :
    ∑ t : F, (a + t * b) ^ (Fintype.card F - 1) = if b = 0 then 0 else 1 := by
  classical
  by_cases hb : b = 0
  · simp [hb, nsmul_eq_mul, FiniteField.cast_card_eq_zero]
  · rw [if_neg hb]
    calc
      _ = ∑ t : F, t ^ (Fintype.card F - 1) :=
        Fintype.sum_bijective (fun t : F => a + t*b)
          ⟨fun x y h => mul_right_cancel₀ hb (add_left_cancel h),
            fun y => ⟨(y-a)/b, by field_simp; ring⟩⟩ _ _ (fun _ => rfl)
      _ = 1 := power_sum
lemma orbit_sum :
    ∑ x : F, ∑ y : F, ∑ z : F, ∑ b : F,
      x ^ (Fintype.card F - 1) * (x*z+y^2+b*y*z) ^ (Fintype.card F - 1) = 1 := by
  classical
  have hp (t : F) : t ^ (Fintype.card F - 1) = if t = 0 then 0 else 1 := by
    split_ifs with ht
    · have : Fintype.card F - 1 ≠ 0 := by have := Fintype.one_lt_card (α := F); omega
      simp [ht, this]
    · exact FiniteField.pow_card_sub_one_eq_one _ ht
  have hi (x y z : F) :
      (∑ b : F, x ^ (Fintype.card F - 1) *
        (x*z+y^2+b*y*z) ^ (Fintype.card F - 1)) =
      x ^ (Fintype.card F - 1) * y ^ (Fintype.card F - 1) *
        z ^ (Fintype.card F - 1) := by
    rw [← Finset.mul_sum]
    simp_rw [mul_assoc]
    rw [affine_sum, hp y, hp z]
    by_cases hy : y = 0 <;> by_cases hz : z = 0 <;> simp [hy, hz]
  simp_rw [hi, ← Finset.mul_sum, power_sum, mul_one, ← Finset.mul_sum, power_sum, mul_one]
  exact power_sum
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.FullOrbit
