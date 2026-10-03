module

public import Mathlib.GroupTheory.Sylow

/-!
# Bounding the index of a Sylow subgroup

If the group order divides `m * p ^ n`, the index of a Sylow `p`-subgroup
divides `m`. Lagrange's theorem gives divisibility by the whole bound, and
the Sylow index is coprime to the power of `p`.

This is a direct consequence of Sylow's theorem and Euclid's lemma.
-/

namespace Sylow

/-- A bound on the prime-to-`p` part of the group order also bounds every
Sylow `p`-index by divisibility. -/
public theorem index_dvd_of_card_dvd_mul_prime_pow
    {G : Type*} [Group G] [Finite G] {p m n : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hcard : Nat.card G ∣ m * p ^ n) : P.index ∣ m := by
  have hd := (P : Subgroup G).index_dvd_card.trans hcard
  exact (Fact.out : p.Prime).coprime_pow_of_not_dvd P.not_dvd_index
    |>.dvd_of_dvd_mul_right hd

end Sylow
