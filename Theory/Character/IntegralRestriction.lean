module

public import Theory.Character.ScalarProductMultiplicity
public import Theory.Character.Transport

/-!
# Integral numerators of character restrictions

The unnormalized pairing of an ordinary character with a generalized
character is the group order times an integer. Thus an integer evaluation
of that pairing is divisible by the group order. Restriction along a group
homomorphism gives the same result for characters of an ambient group.

Source: ordinary character multiplicity and restriction, Serre,
*Linear Representations of Finite Groups*, Chapter 2.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

/-- An integer numerator of a character pairing is divisible by the group order. -/
theorem IsCharacter.card_dvd_pairing_numerator
    {H : Type*} [Group H] [Finite H] {χ η : ClassFunction H}
    (hχ : IsCharacter χ) (hη : IsGeneralizedCharacter η) (z : ℤ)
    (hsum : (∑ h : H, χ h * star (η h)) = (z : ℂ)) :
    (Nat.card H : ℤ) ∣ z := by
  obtain ⟨m, hm⟩ := hχ.scalarProduct_generalized_int hη
  have hc : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have he : (z : ℂ) = (Nat.card H : ℂ) * (m : ℂ) := by
    rw [← hm, scalarProduct, hsum, mul_inv_cancel_left₀ hc]
  exact ⟨m, by exact_mod_cast he⟩

/-- Evaluate a subgroup restriction against any actual generalized character. -/
theorem IsCharacter.card_dvd_restriction_numerator
    {G H : Type*} [Group G] [Group H] [Finite H]
    (e : H →* G) {χ : ClassFunction G} (hχ : IsCharacter χ)
    {η : ClassFunction H} (hη : IsGeneralizedCharacter η) (z : ℤ)
    (hsum : (∑ h : H, χ (e h) * star (η h)) = (z : ℂ)) :
    (Nat.card H : ℤ) ∣ z :=
  (isCharacter_comp_hom e hχ).card_dvd_pairing_numerator hη z hsum

/-- The integer sum of a character restriction is divisible by the group order. -/
theorem IsCharacter.card_dvd_restriction_sum
    {G H : Type*} [Group G] [Group H] [Finite H]
    (e : H →* G) {χ : ClassFunction G} (hχ : IsCharacter χ) (z : ℤ)
    (hsum : (∑ h : H, χ (e h)) = (z : ℂ)) :
    (Nat.card H : ℤ) ∣ z := by
  obtain ⟨m, hm⟩ := (isCharacter_comp_hom e hχ).scalarProduct_nat isCharacter_one
  have hc : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have he : (z : ℂ) = (Nat.card H : ℂ) * (m : ℂ) := by
    simp only [scalarProduct, Pi.one_apply, star_one, mul_one] at hm
    rw [← hm, hsum, mul_inv_cancel_left₀ hc]
  exact ⟨(m : ℤ), by exact_mod_cast he⟩
