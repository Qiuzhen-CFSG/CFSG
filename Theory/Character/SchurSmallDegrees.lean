module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic

/-!
# Numerical specializations of Schur's bound

For a faithful character rational on odd-order elements, Schur's argument
gives the odd Sylow bound `p ^ k * k!`, with `k = d / (p - 1)`.
Here we extract its prime-power part in degrees four, eleven and thirteen,
and combine it with a Sylow two-subgroup of order sixteen.
The character-theoretic Sylow bound is an explicit hypothesis: this module
does not assume a rational realization of a rational-valued character.

Source: Schur (1905), as applied in Alperin--Brauer--Gorenstein,
III.8 Lemmas 1--2 and Proposition 5.
-/

namespace Theory.Character

private theorem prime_pow_dvd_small_degree_bound
    (d B p e : ℕ) (hcase :
      (d = 4 ∧ B = 16 * 3^2 * 5) ∨
      (d = 11 ∧ B = 16 * 3^6 * 5^2 * 7 * 11) ∨
      (d = 13 ∧ B = 16 * 3^8 * 5^3 * 7^2 * 11 * 13))
    (hp : p.Prime) (hodd : p ≠ 2)
    (h : p ^ e ∣ p ^ (d / (p - 1)) * (d / (p - 1)).factorial) :
    p ^ e ∣ B := by
  have hd : d ≤ 13 := by rcases hcase with h | h | h <;> omega
  by_cases hlarge : 14 < p
  · have hk : d / (p - 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp only [hk, pow_zero, Nat.factorial_zero, mul_one] at h
    exact h.trans (one_dvd _)
  have hsmall : p ≤ 14 := by omega
  have hcases : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
    interval_cases p <;> norm_num at hp <;> norm_num
    omega
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;> norm_num at h ⊢
  all_goals first
    | subst e; norm_num
    | exact h.trans (by norm_num)

private theorem card_dvd_small_degree_bound
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (hS : Nat.card S = 16)
    (d B : ℕ) (hcase :
      (d = 4 ∧ B = 16 * 3^2 * 5) ∨
      (d = 11 ∧ B = 16 * 3^6 * 5^2 * 7 * 11) ∨
      (d = 13 ∧ B = 16 * 3^8 * 5^3 * 7^2 * 11 * 13))
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p G,
      Nat.card P ∣ p ^ (d / (p - 1)) * (d / (p - 1)).factorial) :
    Nat.card G ∣ B := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p e hp he
  let : Fact p.Prime := ⟨hp⟩
  by_cases htwo : p = 2
  · subst p
    have h := S.pow_dvd_card_of_pow_dvd_card he
    rw [hS] at h
    apply h.trans
    rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num
  · let P : Sylow p G := Classical.choice inferInstance
    exact prime_pow_dvd_small_degree_bound d B p e hcase hp htwo
      ((P.pow_dvd_card_of_pow_dvd_card he).trans (hodd p htwo P))

/-- The degree-four odd Sylow bounds and a Sylow two-subgroup of order sixteen. -/
public theorem card_dvd_degree_four_bound_of_sylow_bounds
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (hS : Nat.card S = 16)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p G,
      Nat.card P ∣ p ^ (4 / (p - 1)) * (4 / (p - 1)).factorial) :
    Nat.card G ∣ 720 :=
  card_dvd_small_degree_bound S hS 4 720 (Or.inl ⟨rfl, rfl⟩) hodd

/-- The degree-eleven bound, retaining the possible factor seven. -/
public theorem card_dvd_degree_eleven_bound_of_sylow_bounds
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (hS : Nat.card S = 16)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p G,
      Nat.card P ∣ p ^ (11 / (p - 1)) * (11 / (p - 1)).factorial) :
    Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11 :=
  card_dvd_small_degree_bound S hS 11 _ (Or.inr (Or.inl ⟨rfl, rfl⟩)) hodd

/-- The degree-thirteen bound, before excluding primes using the order formula. -/
public theorem card_dvd_degree_thirteen_bound_of_sylow_bounds
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (hS : Nat.card S = 16)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p G,
      Nat.card P ∣ p ^ (13 / (p - 1)) * (13 / (p - 1)).factorial) :
    Nat.card G ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13 :=
  card_dvd_small_degree_bound S hS 13 _ (Or.inr (Or.inr ⟨rfl, rfl⟩)) hodd

end Theory.Character
