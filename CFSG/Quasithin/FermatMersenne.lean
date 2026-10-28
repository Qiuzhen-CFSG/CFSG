module

public import Theory.NumberTheory.FermatMersenne

/-!
# Shared Fermat–Mersenne prime parameters

The model alternatives in Aschbacher–Smith, *The Classification of Quasithin
Groups*, Theorem 0.1.2 and Lemma I.4.1 (combined manuscript, 1 March 2004,
printed pp. 4 and 415) use the same Fermat or Mersenne primes. This common
interface retains the successor presentation used by the models and proves
its equivalence to the prime-exponent presentation used by the arithmetic.
The conversion uses the Mersenne factorization lemma in the lower arithmetic
layer; it introduces no additional restriction on the model parameters.
-/

namespace CFSG.Quasithin

/-- A Fermat or Mersenne prime, including 3, 5, and 7. The separate restriction
`5 ≤ p` in the simple `PSL₂(p)` model branch excludes nonsimple `PSL₂(3)`. -/
@[expose] public def IsFermatOrMersennePrime (p : ℕ) : Prop :=
  p.Prime ∧ ((∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) ∨ (∃ k : ℕ, p + 1 = 2 ^ k))

/-- The shared predicate retains the prime-exponent information of the
Mersenne alternative. Both directions preserve the Fermat alternative. -/
public theorem isFermatOrMersennePrime_iff_prime_exponent {p : ℕ} :
    IsFermatOrMersennePrime p ↔
      p.Prime ∧ ((∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) ∨
        ∃ k : ℕ, k.Prime ∧ p = 2 ^ k - 1) := by
  unfold IsFermatOrMersennePrime
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, h.imp id hp.exists_add_one_eq_two_pow_iff.mp⟩
  · rintro ⟨hp, h⟩
    exact ⟨hp, h.imp id hp.exists_add_one_eq_two_pow_iff.mpr⟩

end CFSG.Quasithin
