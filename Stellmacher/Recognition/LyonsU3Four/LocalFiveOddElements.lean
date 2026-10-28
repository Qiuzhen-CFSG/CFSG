module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveLinearCharacters

/-!
# Odd-order elements of the Lyons local group

An odd-order element in the Sylow kernel is trivial. This common interface
allows the quartic and quintic character constructions to be imported together.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four
variable {G : Type*} [Group G] (S : Sylow 2 G)
    (α : FiveComplement →* MulAut S)

/-- An odd-order element in the Sylow kernel is the identity. -/
theorem localFive_odd_right_eq_one_iff (u : LocalFiveGroup S α)
    (hu : Odd (orderOf u)) : u.right = 1 ↔ u = 1 := by
  constructor
  · intro hr
    have he : SemidirectProduct.inl u.left = u := by
      simpa [hr] using (SemidirectProduct.inl_left_mul_inr_right u)
    have ho : Odd (orderOf u.left) := by
      rw [← he, orderOf_injective _ SemidirectProduct.inl_injective] at hu
      exact hu
    have hl : u.left = 1 := by
      by_contra hn
      exact ho.not_two_dvd_nat (S.isPGroup'.dvd_orderOf hn)
    rw [← he, hl, map_one]
  · rintro rfl
    rfl

end Stellmacher.Recognition.LyonsU3Four
