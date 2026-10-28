module

public import Mathlib.Tactic

/-!
# The degree calculation for characteristic three

The signed degrees in III.2 satisfy `1 + z₁ + z₂ + z₃ = 0` and
`z₁ z₂ = 9 z₃`. Thus `(z₁ + 9)(z₂ + 9) = 72`. The two congruences
modulo sixteen leave exactly the two possibilities in III.8 Proposition 1.
The group-order identity is kept as a separate, explicit input: this
arithmetic does not construct characters or establish block membership.

Source: Alperin--Brauer--Gorenstein, III.2 Proposition 6, equations (5)--(6),
and III.8 Proposition 1, article pp.69 and 111.
-/

namespace ABG

/-- Clearing the blockwise involution-pair identity gives the degree product.
The two congruences exclude the only factor that could prevent cancellation. -/
public theorem three_principal_product_of_pairing (z₁ z₂ z₃ : ℤ)
    (hsum : 1 + z₁ + z₂ + z₃ = 0)
    (h₁ : 16 ∣ z₁ - 5) (h₂ : 16 ∣ z₂ - 3)
    (hpair : z₁ * z₂ * z₃ + 9 * z₂ * z₃ + 9 * z₁ * z₃ + z₁ * z₂ = 0) :
    z₁ * z₂ = 9 * z₃ := by
  have hf : (z₃ + 1) * (z₁ * z₂ - 9 * z₃) = 0 := by
    linear_combination hpair - 9 * z₃ * hsum
  have hn : z₃ + 1 ≠ 0 := by
    intro he
    omega
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hn)

/-- The signed odd degrees forced by the principal-block identities at `q = 3`.
No degree bounds or numerical character table are assumed. -/
public theorem three_principal_signed_degrees (z₁ z₂ z₃ : ℤ)
    (hsum : 1 + z₁ + z₂ + z₃ = 0) (hprod : z₁ * z₂ = 9 * z₃)
    (h₁ : 16 ∣ z₁ - 5) (_h₂ : 16 ∣ z₂ - 3) :
    (z₁ = -11 ∧ z₂ = -45 ∧ z₃ = 55) ∨
      (z₁ = -27 ∧ z₂ = -13 ∧ z₃ = 39) := by
  have hfactor : (z₁ + 9) * (z₂ + 9) = 72 := by nlinarith only [hsum, hprod]
  have hdiv : z₁ + 9 ∣ 72 := ⟨z₂ + 9, hfactor.symm⟩
  have hb := Int.natAbs_le_of_dvd_ne_zero hdiv (by norm_num : (72 : ℤ) ≠ 0)
  have hlo : -81 ≤ z₁ := by omega
  have hhi : z₁ ≤ 63 := by omega
  have hcases : z₁ = -11 ∨ z₁ = -27 := by
    interval_cases z₁ <;> norm_num at *
  rcases hcases with rfl | rfl
  · left
    constructor
    · rfl
    · constructor <;> nlinarith only [hfactor, hsum]
  · right
    constructor
    · rfl
    · constructor <;> nlinarith only [hfactor, hsum]

/-- After resolving the signs, the five positive degrees have two possibilities. -/
public theorem three_principal_degrees (f₁ f₂ f₃ f₄ f : ℕ)
    (hsum : 1 + f₃ = f₁ + f₂) (hprod : f₁ * f₂ = 9 * f₃)
    (h₁ : f₁ % 16 = 11) (h₂ : f₂ % 16 = 13)
    (h₄ : f₄ + 1 = f₂) (hf : f + 1 = f₁) :
    (f₁ = 11 ∧ f₂ = 45 ∧ f₃ = 55 ∧ f₄ = 44 ∧ f = 10) ∨
      (f₁ = 27 ∧ f₂ = 13 ∧ f₃ = 39 ∧ f₄ = 12 ∧ f = 26) := by
  have hs : 1 + -(f₁ : ℤ) + -(f₂ : ℤ) + (f₃ : ℤ) = 0 := by omega
  have hp : -(f₁ : ℤ) * -(f₂ : ℤ) = 9 * (f₃ : ℤ) := by
    simpa only [neg_mul_neg, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℤ)) hprod
  have hc₁ : 16 ∣ -(f₁ : ℤ) - 5 := by omega
  have hc₂ : 16 ∣ -(f₂ : ℤ) - 3 := by omega
  rcases three_principal_signed_degrees _ _ _ hs hp hc₁ hc₂ with h | h
  · left
    omega
  · right
    omega

/-- The first ABG order formula, with `|N| = 48ab` and `|C| = 4a`
already substituted and denominators cleared, gives the two orders. -/
public theorem three_principal_degree_order_alternatives
    (g a b f₁ f₂ f₃ f₄ f : ℕ)
    (hsum : 1 + f₃ = f₁ + f₂) (hprod : f₁ * f₂ = 9 * f₃)
    (h₁ : f₁ % 16 = 11) (h₂ : f₂ % 16 = 13)
    (h₄ : f₄ + 1 = f₂) (hf : f + 1 = f₁)
    (horder : (g : ℤ) * ((f₁ : ℤ) - 3)^2 =
      4608 * (a * b^3 : ℕ) * (f₁ : ℤ) * ((f₁ : ℤ) - 1)) :
    (f₁ = 11 ∧ f₂ = 45 ∧ f₃ = 55 ∧ f₄ = 44 ∧ f = 10 ∧
      g = 7920 * (a * b^3)) ∨
    (f₁ = 27 ∧ f₂ = 13 ∧ f₃ = 39 ∧ f₄ = 12 ∧ f = 26 ∧
      g = 5616 * (a * b^3)) := by
  rcases three_principal_degrees f₁ f₂ f₃ f₄ f hsum hprod h₁ h₂ h₄ hf with
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
  · left
    norm_num at horder ⊢
    exact_mod_cast (show (g : ℤ) = 7920 * (a * b^3 : ℕ) by
      push_cast
      linarith only [horder])
  · right
    norm_num at horder ⊢
    exact_mod_cast (show (g : ℤ) = 5616 * (a * b^3 : ℕ) by
      push_cast
      linarith only [horder])

end ABG
