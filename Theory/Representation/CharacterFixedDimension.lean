module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.Analysis.Complex.Basic

/-!
# Fixed dimensions from character sums

The average of the character is the dimension of the fixed space. This
integer-valued form lets a subgroup element census determine the dimension
without repeatedly managing division and complex casts.
Source: the standard averaging projection, as formalized by
`Representation.card_inv_mul_sum_char_eq_finrank`.
-/

namespace Representation

open scoped BigOperators

variable {H V : Type*} [Group H] [Fintype H] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V]

/-- A character sum equal to the order times `d` gives a `d`-dimensional fixed space. -/
public theorem finrank_invariants_eq_of_sum_character
    (ρ : Representation ℂ H V) (d : ℕ)
    (hsum : ∑ h : H, ρ.character h = (Nat.card H : ℂ) * (d : ℂ)) :
    Module.finrank ℂ ρ.invariants = d := by
  let : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have havg := ρ.card_inv_mul_sum_char_eq_finrank
  rw [hsum, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')] at havg
  exact_mod_cast havg.symm

end Representation
