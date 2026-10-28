module

public import Theory.GroupTheory.PResidual.PrimeSet

/-!
# The residual for an empty set of primes

In a finite group, a quotient with no prime divisors has order one. Thus
O^∅(G) = G, including the convention stated before Aschbacher--Smith C.1.10.
-/

public section


theorem piResidual_empty_eq_top (G : Type*) [Group G] [Finite G] :
    piResidual ∅ G = ⊤ := by
  apply (piResidual_eq_top_iff _ _).mpr
  intro N hn hp
  let := hn
  have hcard : Nat.card (G ⧸ N) = 1 := by
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro p hp' hd
    exact (IsPiGroup_iff _ _).mp hp ⟨p, hp'⟩ hd
  apply QuotientGroup.subsingleton_iff.mp
  exact Nat.card_eq_one_iff_unique.mp hcard |>.1
