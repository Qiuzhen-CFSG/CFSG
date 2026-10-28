module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Endomorphisms fixing squares in a cyclic group of order eight

Such an endomorphism is either the identity or the fifth-power map. A cyclic
endomorphism is a power map, and fixing the square of a generator says that
its exponent is congruent to one modulo four.

This is the elementary cyclic-group step in Suzuki, *A characterization of the
3-dimensional projective unitary group over a finite field of odd
characteristic* (1965), Section II, Lemma 7, specialized to q = 3.
-/

namespace MonoidHom

/-- The only endomorphisms of a cyclic group of order eight fixing all squares
are the identity and the fifth-power map. -/
public theorem eq_id_or_pow_five_of_card_eight_of_sq_fixed
    {K : Type*} [Group K] [IsCyclic K] (hcard : Nat.card K = 8)
    (f : K →* K) (hsq : ∀ k : K, f (k ^ 2) = k ^ 2) :
    (∀ k : K, f k = k) ∨ (∀ k : K, f k = k ^ 5) := by
  obtain ⟨m, hm⟩ := f.map_cyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  rw [hcard] at hg
  have hpow : g ^ ((2 : ℤ) * m) = g ^ (2 : ℤ) := by
    simpa only [hm, ← zpow_natCast, ← zpow_mul, Nat.cast_ofNat] using hsq g
  have hmod := zpow_eq_zpow_iff_modEq.mp hpow
  rw [hg] at hmod
  change (2 * m) % 8 = 2 % 8 at hmod
  have hm_cases : m % 8 = 1 ∨ m % 8 = 5 := by omega
  have hreduce (k : K) : f k = k ^ (m % 8) := by
    simpa only [hcard, Nat.cast_ofNat] using (hm k).trans (zpow_mod_natCard k m).symm
  rcases hm_cases with he | he
  · exact Or.inl (fun k => by rw [hreduce, he, zpow_one])
  · exact Or.inr (fun k => by rw [hreduce, he]; exact zpow_ofNat k 5)

/-- Nonidentity singles out the fifth-power map. -/
public theorem eq_pow_five_of_card_eight_of_sq_fixed_of_ne_id
    {K : Type*} [Group K] [IsCyclic K] (hcard : Nat.card K = 8)
    (f : K →* K) (hsq : ∀ k : K, f (k ^ 2) = k ^ 2)
    (hne : ∃ k : K, f k ≠ k) : ∀ k : K, f k = k ^ 5 := by
  rcases f.eq_id_or_pow_five_of_card_eight_of_sq_fixed hcard hsq with hid | hfive
  · obtain ⟨k, hk⟩ := hne
    exact (hk (hid k)).elim
  · exact hfive

end MonoidHom
