module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Basic
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# The exceptional field order eight in the Suzuki fusion argument

The Frobenius degree inequality forces the Suzuki exponent to be three.
At q = 8 the source order bound |D| dividing 294 gives |M| dividing
2^10 * 3² * 7² * 19. Its nontrivial odd prime-power divisors are not
congruent to one modulo seven. The proof uses prime factorizations,
without a large finite enumeration.

The model assertion |J| = 14 and the consequent bound on |D| must still
be supplied; neither is assumed to follow from the degree inequality.
Source: GLS4, Chapter 2, the last two paragraphs of Lemma 14.9,
`refs/KGroup/GLS4/Chapter2.tex`.
-/

namespace BenderSuzuki.ZD.SuzukiExclusion

/-- The only positive Suzuki parameter satisfying the Frobenius degree bound is m = 1. -/
public theorem parameter_eq_one_of_degree_bound {m : ℕ} (hm : 1 ≤ m)
    (hbound : 2 ^ (2 * m + 1) - 1 ≤ 2 * (2 * m + 1) + 1) : m = 1 := by
  have hgrowth (n : ℕ) (hn : 4 ≤ n) : 2 * n + 2 < 2 ^ n := by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [pow_succ]
      omega
  by_contra hm1
  have hn : 4 ≤ 2 * m + 1 := by omega
  have hh := hgrowth (2 * m + 1) hn
  omega

private theorem primePower_ne_one_mod_seven {p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hdiv : p ^ a ∣ 3 ^ 2 * 7 ^ 2 * 19) : ¬ 7 ∣ p ^ a - 1 := by
  have hpdiv : p ∣ 3 ^ 2 * 7 ^ 2 * 19 :=
    (dvd_pow_self p (Nat.ne_of_gt ha)).trans hdiv
  have hp_cases : p = 3 ∨ p = 7 ∨ p = 19 := by
    rcases hp.dvd_mul.mp hpdiv with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · exact Or.inl (((Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp
          (hp.dvd_of_dvd_pow h)).resolve_left hp.ne_one)
      · exact Or.inr (Or.inl (((Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp
          (hp.dvd_of_dvd_pow h)).resolve_left hp.ne_one))
    · exact Or.inr (Or.inr (((Nat.dvd_prime (by norm_num : Nat.Prime 19)).mp h).resolve_left
        hp.ne_one))
  rcases hp_cases with rfl | rfl | rfl
  all_goals
    have hexp := (hp.pow_dvd_iff_le_factorization (by norm_num : 3 ^ 2 * 7 ^ 2 * 19 ≠ 0)).mp hdiv
    rw [Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_pow, Nat.factorization_pow] at hexp
    norm_num [Nat.prime_three.factorization, (by norm_num : Nat.Prime 7).factorization,
      (by norm_num : Nat.Prime 19).factorization] at hexp
    interval_cases a <;> norm_num at *

variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G} {z t : G}

/-- Apply the odd-prime-power sieve to the source point stabilizer at q = 8. -/
public theorem Context.no_odd_primePower_congruence_at_eight
    (d : Context Z M z t 1) (hD : Nat.card (residualPairStabilizer M t) ∣ 294)
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a)
    (hdiv : p ^ a ∣ Nat.card M) : ¬ 7 ∣ p ^ a - 1 := by
  have hM : Nat.card M ∣ 2 ^ 10 * (3 ^ 2 * 7 ^ 2 * 19) := by
    rw [d.card_pointStabilizer]
    convert Nat.mul_dvd_mul_left 29184 hD using 1 <;> norm_num
  have hc : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr (fun h =>
    hp2 (((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hp.ne_one))
  exact primePower_ne_one_mod_seven hp ha
    (((hc.pow_left a).pow_right 10).dvd_of_dvd_mul_left (hdiv.trans hM))

end BenderSuzuki.ZD.SuzukiExclusion
