module

public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Quadratic action on the units of a binary field

A field automorphism acting quadratically on all nonzero elements is identity.
The multiplicative identity is `σ²(x) * x = σ(x)²`. Applying it to `x + 1`
and subtracting the identity for `x` gives `σ²(x) = x` in characteristic two;
injectivity of squaring then gives `σ(x) = x`.

This is the field calculation used for rank-one Cartan complements in
Aschbacher–Smith, F.1.3(5), printed p.260. No finiteness or order hypothesis
on the field automorphism is needed.
-/

public section
namespace RingEquiv

theorem eq_one_of_quadratic_identity {F : Type*} [Field F] [CharP F 2]
    (σ : F ≃+* F) (h : ∀ x : F, σ (σ x) * x = (σ x) ^ 2) : σ = 1 := by
  have hh (x : F) : σ (σ x) = x := by
    have he := h (x + 1)
    simp only [map_add, map_one] at he
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination he - h x + h2 * (σ x - x)
  ext x
  have hx : (σ x - x) ^ 2 = 0 := by
    have he := h x
    rw [hh] at he
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination -he + h2 * (x ^ 2 - σ x * x)
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hx)

/-- A quadratic coefficient action on the full multiplicative torus is trivial. -/
theorem eq_one_of_quadratic_units {F : Type*} [Field F] [CharP F 2]
    (σ : F ≃+* F)
    (h : ∀ u : Fˣ, Units.map σ.toMonoidHom
      (Units.map σ.toMonoidHom u * u⁻¹) = Units.map σ.toMonoidHom u * u⁻¹) :
    σ = 1 := by
  apply eq_one_of_quadratic_identity σ
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have he := congrArg Units.val (h (Units.mk0 x hx))
    change σ (σ x * x⁻¹) = σ x * x⁻¹ at he
    rw [map_mul, map_inv₀] at he
    have hs : σ x ≠ 0 := (map_ne_zero σ).mpr hx
    field_simp at he
    simpa [pow_two] using he

end RingEquiv
