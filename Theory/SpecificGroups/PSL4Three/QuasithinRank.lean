module

public import Theory.GroupTheory.PrimeRankCubeFree
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The nondefining odd-prime ranks of PSL₄(3)

The determinant-kernel and scalar-center order formula gives
|PSL₄(3)| = 6065280 = 2⁷ · 3⁶ · 5 · 13. Thus every odd prime other than
three has rank at most two. The defining-prime bound must be established
inside actual two-local subgroups; no ordinary three-rank bound is asserted.

Source: Aschbacher–Smith, Theorem 0.1.2(4), printed pp.4 and 482.
-/

namespace Matrix.PSL4Three

local notation "PSL" => ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)

/-- The order of the actual matrix quotient PSL₄(3). -/
public theorem card_PSL : Nat.card PSL = 6065280 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 3) 4
  have hF : Nat.card (ZMod 3) = 3 := Nat.card_zmod 3
  rw [hF] at h
  norm_num [Fin.prod_univ_succ] at h
  rw [Nat.card_eq_fintype_card]
  omega

/-- All odd primes except the defining prime have rank at most two. -/
public theorem odd_primeRank_le_two_of_ne_three {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (h3 : p ≠ 3) : primeRank p PSL ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_two_of_cube_not_dvd
  rw [card_PSL]
  intro hd
  have hpd : p ∣ 2 ^ 7 * (3 ^ 6 * (5 * 13)) := by
    norm_num
    exact (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  have hpv : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 13 := by
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

end Matrix.PSL4Three
