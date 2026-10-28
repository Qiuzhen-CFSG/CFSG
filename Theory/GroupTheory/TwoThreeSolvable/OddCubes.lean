module

public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.GroupTheory.PRegularLift

/-!
# Solvability from central cubes of odd-order elements

If every odd-order element of a finite group has central cube, then its central
quotient has no prime divisors except two and three. Cauchy's theorem and an
odd-order lift through the literal quotient map prove this prime support claim.
The two-and-three case of Burnside's theorem then proves solvability.

This is the final group-theoretic inference of GLS, *The Classification of the
Finite Simple Groups*, vol. 2, Theorem 26.24 Step 2;
`refs/KGroup/GLS2/ChapterG.tex`, lines 1225–1230.
-/

public section

open Subgroup
namespace Theory.GroupTheory

/-- If every odd-order element has central cube, the central quotient is solvable. -/
theorem isSolvable_center_quotient_of_odd_cube_central
    {H : Type*} [Group H] [Finite H]
    (hc : ∀ x : H, Odd (orderOf x) → x ^ 3 ∈ center H) :
    Group.IsSolvable (H ⧸ center H) := by
  apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hpd
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  right
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := H ⧸ center H) p hpd
  let π := QuotientGroup.mk' (center H)
  obtain ⟨x, hx, hxq⟩ := π.exists_pRegular_lift (QuotientGroup.mk'_surjective _) 2
    Nat.prime_two q (by rw [hq]; exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm)
  have hxodd : Odd (orderOf x) := Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hx)
  have hq3 : q ^ 3 = 1 := by
    rw [← hxq, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hc x hxodd)
  have hp3 : p ∣ 3 := hq ▸ orderOf_dvd_iff_pow_eq_one.mpr hq3
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3

end Theory.GroupTheory
