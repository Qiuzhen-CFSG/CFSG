module

public import Theory.SpecificGroups.SymplecticSix.Basic
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder.PairRecurrence
public import Theory.GroupTheory.PrimeRankCubeFree

/-!
# The binary symplectic order and odd ranks away from three

The proved hyperbolic-pair recurrence gives |Sp₆(2)| = 1451520.
Its prime factorization is 2⁹ · 3⁴ · 5 · 7, so every odd prime other than
three has rank at most two. The three-rank must be bounded inside actual
two-local subgroups; no global three-rank bound is asserted here.

Source: the pair-counting argument attributed in `PairRecurrence.lean`.
This supplies the elementary non-three branches of Aschbacher–Smith,
Theorem 0.1.2(2), printed p.4 (Theorem 0.1.1(2), printed p.482).
-/

namespace Theory.SpecificGroups.SymplecticSix

variable {F : Type*} [Field F] [Finite F]

/-- Order of the actual six-dimensional matrix group over a binary field. -/
public theorem card_sp_of_card_two (hF : Nat.card F = 2) :
    Nat.card (Sp F) = 1451520 := by
  change Nat.card (Matrix.symplecticGroup (Fin (2 + 1)) F) = _
  rw [SymplecticFour.AmbientOrderProof.card_sp_succ,
    SymplecticFour.AmbientOrderProof.card_sp_succ (n := 1),
    SymplecticFour.AmbientOrderProof.card_sp_succ (n := 0)]
  have hzero : Nat.card (Matrix.symplecticGroup (Fin 0) F) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  norm_num [hF, hzero]

/-- Only three requires a local odd-rank argument for the binary matrix group. -/
public theorem odd_primeRank_le_two_of_ne_three (hF : Nat.card F = 2)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (h3 : p ≠ 3) :
    primeRank p (Sp F) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_two_of_cube_not_dvd
  rw [card_sp_of_card_two hF]
  intro hd
  have hpd : p ∣ 2 ^ 9 * (3 ^ 4 * (5 * 7)) := by
    norm_num
    exact (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  have hpv : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    rcases hp.dvd_mul.mp hpd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow h))
    rcases hp.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow h)))
    rcases hp.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)))
    · exact Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)))
  rcases hpv with rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  · exact h3 rfl
  all_goals norm_num at hd

end Theory.SpecificGroups.SymplecticSix
