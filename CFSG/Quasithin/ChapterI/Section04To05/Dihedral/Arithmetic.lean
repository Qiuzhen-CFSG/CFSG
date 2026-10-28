module

public import BenderSuzuki.PFchapter2.claim_6
public import CFSG.Quasithin.FermatMersenne

/-!
# The prime restriction in I.4.1

Aschbacher–Smith, *The Classification of Quasithin Groups*, I.4.1, printed
p. 415, deduces the Fermat/Mersenne restriction from a two-group involution
centralizer in odd-characteristic PSL₂. This module proves the arithmetic
step: an odd prime power adjacent to `2 ^ n` is a Fermat or Mersenne prime,
except for `9 = 8 + 1`. In particular the exception is impossible for `n > 3`.

The proof specializes the checked prime-power successor trichotomy in
`BenderSuzuki.PFchapter2.claim_6` (Huppert–Blackburn IX.2.7). The conversion
from a PSL₂ centralizer to the numerical hypotheses is a separate step.
-/

namespace CFSG.Quasithin

/-- An odd prime power adjacent to a power of two is prime, except for nine. -/
public theorem prime_power_two_power_neighbors
    {p k n : ℕ} (hp : p.Prime) (hpodd : Odd p) (hk : 1 ≤ k)
    (hn : 2 ≤ n) (h : p ^ k + 1 = 2 ^ n ∨ p ^ k = 2 ^ n + 1) :
    (k = 1 ∧ IsFermatOrMersennePrime p) ∨ (p ^ k = 9 ∧ n = 3) := by
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    norm_num at hpodd
  rcases h with h | h
  · rcases BenderSuzuki.PFchapter2.prime_power_successor_trichotomy
        Nat.prime_two hp (by omega) (by omega) h.symm with hm | hf | he
    · exact Or.inl ⟨hm.2.1, isFermatOrMersennePrime_iff_prime_exponent.mpr
        ⟨hp, Or.inr ⟨n, hm.2.2.1, hm.2.2.2⟩⟩⟩
    · exact (hp2 hf.1).elim
    · have hev : Even (2 ^ n) := Even.pow_of_ne_zero even_two (by omega)
      rw [he.1] at hev
      norm_num at hev
  · rcases BenderSuzuki.PFchapter2.prime_power_successor_trichotomy
        hp Nat.prime_two (by omega) (by omega) h with hm | hf | he
    · exact (hp2 hm.1).elim
    · obtain ⟨a, _, ha⟩ := hf.2.2
      exact Or.inl ⟨hf.2.1, hp, Or.inl ⟨a, ha⟩⟩
    · refine Or.inr ⟨he.1, ?_⟩
      apply Nat.pow_right_injective (by omega : 2 ≤ 2)
      simpa using he.2

/-- Above centralizer order eight, the field size is a Fermat or Mersenne prime. -/
public theorem prime_power_two_power_neighbors_of_three_lt
    {p k n : ℕ} (hp : p.Prime) (hpodd : Odd p) (hk : 1 ≤ k)
    (hn : 3 < n) (h : p ^ k + 1 = 2 ^ n ∨ p ^ k = 2 ^ n + 1) :
    k = 1 ∧ IsFermatOrMersennePrime p := by
  rcases prime_power_two_power_neighbors hp hpodd hk (by omega) h with h | h
  · exact h
  · omega

end CFSG.Quasithin
