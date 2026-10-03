module

public import Theory.Character.ClassFunction
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Degree congruences from constant character restrictions

If a character takes the integer value `z` at every nonidentity element of
a finite subgroup `H`, its degree is congruent to `z` modulo `|H|`.
Averaging the restricted representation counts its invariant vectors;
subtracting the constant function `z` leaves only the identity term.

Source application: Brauer, *Some applications of the theory of blocks of
characters of finite groups. II*, J. Algebra 1 (1964), §VI, (6.6)–(6.7).
-/

open scoped BigOperators

public section

/-- The degree of a representation constant off the identity is congruent
to that constant value modulo the group order. -/
theorem Representation.card_dvd_finrank_sub_of_character_constant
    {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ H V) (z : ℤ)
    (hvalue : ∀ h : H, h ≠ 1 → ρ.character h = (z : ℂ)) :
    (Nat.card H : ℤ) ∣ (Module.finrank ℂ V : ℤ) - z := by
  classical
  let := Fintype.ofFinite H
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hcard
  have hs : ∑ h : H, (ρ.character h - (z : ℂ)) =
      (Module.finrank ℂ V : ℂ) - (z : ℂ) := by
    rw [Finset.sum_eq_single 1]
    · rw [ρ.char_one]
    · intro h _ hh
      rw [hvalue h hh, sub_self]
    · simp
  have hm := ρ.card_inv_mul_sum_char_eq_finrank
  have hsum : ∑ h : H, ρ.character h =
      (Nat.card H : ℂ) * (Module.finrank ℂ ρ.invariants : ℂ) := by
    rw [← hm, mul_inv_cancel_left₀ hcard]
  rw [Finset.sum_sub_distrib, hsum] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card] at hs
  refine ⟨(Module.finrank ℂ ρ.invariants : ℤ) - z, ?_⟩
  have he : (Module.finrank ℂ V : ℂ) - (z : ℂ) =
      (Nat.card H : ℂ) * ((Module.finrank ℂ ρ.invariants : ℂ) - (z : ℂ)) := by
    rw [mul_sub]
    exact hs.symm
  exact_mod_cast he

/-- A subgroup on which a character is constant off the identity gives a
congruence for its integer degree. -/
theorem IsCharacter.card_dvd_degree_sub_of_constant
    {G : Type*} [Group G] (H : Subgroup G) [Finite H]
    {χ : ClassFunction G} (hχ : IsCharacter χ) (a z : ℤ)
    (hdegree : χ 1 = (a : ℂ))
    (hvalue : ∀ g ∈ H, g ≠ 1 → χ g = (z : ℂ)) :
    (Nat.card H : ℤ) ∣ a - z := by
  obtain ⟨n, ρ, rfl⟩ := hχ
  have hn : (n : ℤ) = a := by
    have hnC : (n : ℂ) = (a : ℂ) := by
      simpa only [Representation.char_one, Module.finrank_pi, Module.finrank_self,
        Fintype.card_fin, mul_one] using hdegree
    exact_mod_cast hnC
  have h := Representation.card_dvd_finrank_sub_of_character_constant
    (ρ.comp H.subtype) z (by
    intro g hg
    exact hvalue g g.property (fun heq => hg (Subtype.ext heq)))
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one, hn]
    using h
