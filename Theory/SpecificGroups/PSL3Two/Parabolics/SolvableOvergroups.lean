module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.GroupTheory.SolvableSylowOvergroups
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# Solvable proper Sylow overgroups in PSL₃(2)

The binary Bruhat decomposition places a proper Sylow overgroup in one of
the two parabolics of order 24. Its order therefore has only primes two and
three, so the proved two-prime theorem gives solvability.

Source/application: Aschbacher–Smith, 13.1.2(5), printed p.866.
-/

public section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Two

/-- The literal projective matrix group has solvable proper Sylow overgroups. -/
theorem solvableSylowOvergroups : SolvableSylowOvergroups PSL := by
  intro S H hSH hH
  obtain ⟨P,L,_,_,_,_,hP,hL,hmax⟩ := sylow_parabolics S
  obtain ⟨M,hM,hHM⟩ := (eq_top_or_exists_le_coatom H).resolve_left hH
  have hc : Nat.card H ∣ 24 := by
    rcases (hmax M hM).mp (hSH.trans hHM) with he | he
    · simpa only [he,hP] using card_dvd_of_le hHM
    · simpa only [he,hL] using card_dvd_of_le hHM
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  have hd24 := hd.trans hc
  have h : p ∣ 2 ^ 3 * 3 := hd24
  rcases hp.dvd_mul.mp h with h | h
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      |>.resolve_left hp.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hp.ne_one)
end Matrix.PSL3Two
