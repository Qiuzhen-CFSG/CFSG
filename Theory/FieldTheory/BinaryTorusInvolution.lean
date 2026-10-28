module

public import Theory.NumberTheory.BinaryTorusParity
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A quadratic binary field action on the multiplicative torus

For |F| = 2^(2m), the automorphism x ↦ x^(2^m) has displacement
u ↦ σ(u)u⁻¹ equal to the `(2^m-1)` power map on Fˣ. Cyclicity of Fˣ
therefore gives image order 2^m+1. If σ fixes the three-residual,
this image is a three-group, which forces m = 1 or m = 3.
For m > 1 the displacement image has order greater than three.

Source: the field-torus calculation in Aschbacher–Smith, proof of 13.8.20,
printed p.954. The hypothesis specifying the field action is explicit;
identification of an automorphism of a matrix group with this action must
be proved separately. No matrix-group centralizer is assumed here.
-/

@[expose] public section

namespace FiniteField.BinaryTorusInvolution
variable {F : Type*} [Field F]

def displacement (σ : F ≃+* F) : Fˣ →* Fˣ where
  toFun u := Units.map σ.toMonoidHom u * u⁻¹
  map_one' := by simp
  map_mul' u v := by simp [mul_comm, mul_left_comm, mul_assoc]

theorem displacement_eq_power (σ : F ≃+* F) {m : ℕ}
    (hσ : ∀ x : F, σ x = x ^ (2 ^ m)) :
    displacement σ = powMonoidHom (2 ^ m - 1) := by
  apply MonoidHom.ext
  intro u
  have he : Units.map σ.toMonoidHom u = u ^ (2 ^ m) := Units.ext (hσ u)
  change Units.map σ.toMonoidHom u * u⁻¹ = u ^ (2 ^ m - 1)
  rw [he, pow_sub _ (Nat.one_le_pow _ _ (by decide : 1 ≤ (2 : ℕ))), pow_one]

variable [Finite F]

theorem card_displacement (σ : F ≃+* F) {m : ℕ} (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m))
    (hσ : ∀ x : F, σ x = x ^ (2 ^ m)) :
    Nat.card (displacement σ).range = 2 ^ m + 1 := by
  rw [displacement_eq_power σ hσ, IsCyclic.card_powMonoidHom_range, Nat.card_units, hF]
  have hpow : (2 : ℕ) ^ (2 * m) - 1 = (2 ^ m - 1) * (2 ^ m + 1) := by
    rw [mul_comm 2 m, pow_mul]
    simpa only [one_pow, mul_comm] using Nat.sq_sub_sq (2 ^ m) 1
  have hpos : 0 < (2 : ℕ) ^ m - 1 := by
    have := one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega : m ≠ 0)
    omega
  rw [hpow, Nat.gcd_eq_right (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hpos]

theorem displacement_isThreeGroup_of_fixed_residual (σ : F ≃+* F)
    (hfix : ∀ u ∈ pResidual 3 Fˣ, Units.map σ.toMonoidHom u = u) :
    IsPGroup 3 (displacement σ).range := by
  have hk : pResidual 3 Fˣ ≤ (displacement σ).rangeRestrict.ker := by
    intro u hu
    apply Subtype.ext
    change Units.map σ.toMonoidHom u * u⁻¹ = 1
    rw [hfix u hu, mul_inv_cancel]
  let f := QuotientGroup.lift (pResidual 3 Fˣ) (displacement σ).rangeRestrict hk
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨u, hu⟩ := (displacement σ).rangeRestrict_surjective v
    exact ⟨QuotientGroup.mk u, hu⟩
  exact (Subgroup.isPGroup_quotient_pResidual 3).of_surjective f hf

theorem half_degree_of_fixed_residual (σ : F ≃+* F) {m : ℕ} (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m))
    (hσ : ∀ x : F, σ x = x ^ (2 ^ m))
    (hfix : ∀ u ∈ pResidual 3 Fˣ, Units.map σ.toMonoidHom u = u) :
    m = 1 ∨ m = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (displacement_isThreeGroup_of_fixed_residual σ hfix).exists_card_eq
  rw [card_displacement σ hm hF hσ] at hk
  exact Nat.BinaryTorusParity.plus_three_power_degree hm hk

theorem displacement_card_gt_three (σ : F ≃+* F) {m : ℕ} (hm : 1 < m)
    (hF : Nat.card F = 2 ^ (2 * m))
    (hσ : ∀ x : F, σ x = x ^ (2 ^ m)) :
    3 < Nat.card (displacement σ).range := by
  rw [card_displacement σ (by omega) hF hσ]
  have := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hm
  norm_num at this
  omega

end FiniteField.BinaryTorusInvolution
