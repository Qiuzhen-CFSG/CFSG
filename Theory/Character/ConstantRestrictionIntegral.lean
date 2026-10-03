module

public import Theory.Character.Divisibility
public import Theory.Character.ConstantRestriction
public import Mathlib.Tactic.FieldSimp

/-!
# Integrality of a constant character restriction

A character constant off the identity of a nontrivial finite group has an
integer constant value. Averaging expresses that value as the rational
number `(|H| dim Vᴴ - dim V) / (|H| - 1)`. Character values are algebraic
integers, so rationality implies integrality over the ordinary integers.

Source application: Fong (1967), printed p.75, cyclic five-block case.
-/

public section
open scoped BigOperators

/-- A constant character value away from the identity is an integer. -/
theorem Representation.exists_int_of_character_constant
    {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ H V)
    (hcard : 1 < Nat.card H) (c : ℂ)
    (hv : ∀ h : H, h ≠ 1 → ρ.character h = c) : ∃ z : ℤ, c = (z : ℂ) := by
  classical
  let := Fintype.ofFinite H
  let : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨u, hu⟩ := exists_ne (1 : H)
  have hint : IsIntegral ℤ c := hv u hu ▸ representation_character_isIntegral ρ u
  apply hint.exists_int_iff_exists_rat.mp
  have h0 : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let : Invertible (Nat.card H : ℂ) := invertibleOfNonzero h0
  have hs : ∑ h : H, (ρ.character h - c) = (Module.finrank ℂ V : ℂ) - c := by
    rw [Finset.sum_eq_single 1]
    · rw [ρ.char_one]
    · intro h _ hh
      rw [hv h hh, sub_self]
    · simp
  have hm := ρ.card_inv_mul_sum_char_eq_finrank
  have hsum : ∑ h : H, ρ.character h =
      (Nat.card H : ℂ) * (Module.finrank ℂ ρ.invariants : ℂ) := by
    rw [← hm, mul_inv_cancel_left₀ h0]
  rw [Finset.sum_sub_distrib, hsum] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card] at hs
  refine ⟨((Nat.card H : ℚ) * (Module.finrank ℂ ρ.invariants : ℚ) -
    (Module.finrank ℂ V : ℚ)) / ((Nat.card H : ℚ) - 1), ?_⟩
  have h1 : (Nat.card H : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (show (Nat.card H : ℤ) - 1 ≠ 0 by omega)
  push_cast
  apply (eq_div_iff h1).mpr
  linear_combination -hs
