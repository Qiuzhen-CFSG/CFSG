module
public import GorensteinWalter.PSL2Cardinality
public import Theory.GroupTheory.PrimeRankZero

/-!
# Nontrivial three-rank in odd prime-field PSL₂

The order formula p(p² - 1)/2 is divisible by three: its numerator is
six-divisible, as checked by the six residue classes. Vanishing prime rank
is equivalent to prime-to-three order, giving the required rank lower bound.
Source application: Aschbacher--Smith 12.4.8, printed p.815, the two-component
rank obstruction in the ordinary-component branch.
-/
public section
open scoped MatrixGroups
namespace Theory.PSL2

private theorem six_dvd_cubic_order (p : ℕ) (hp : 1 ≤ p) : 6 ∣ p * (p ^ 2 - 1) := by
  have hpowpos : 1 ≤ p ^ 2 := one_le_pow₀ hp
  have hm : p % 6 < 6 := Nat.mod_lt p (by decide)
  have hcases : p % 6 = 0 ∨ p % 6 = 1 ∨ p % 6 = 2 ∨
      p % 6 = 3 ∨ p % 6 = 4 ∨ p % 6 = 5 := by omega
  apply Nat.dvd_of_mod_eq_zero
  rcases hcases with h | h | h | h | h | h
  all_goals
    have hpmod := Nat.pow_mod p 2 6
    rw [h] at hpmod
    norm_num at hpmod
    have hsub : (p ^ 2 - 1) % 6 = (p ^ 2 % 6 + 5) % 6 := by omega
    norm_num only [Nat.mul_mod,h,hsub,hpmod]

theorem prime_model_three_dvd_card {Q : Type*} [Group Q]
    {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p) (e : Q ≃* PSL(2,F)) : 3 ∣ Nat.card Q := by
  rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
    ⟨p,1,hp,ho,by decide,by simpa only [pow_one] using hF⟩,hF]
  obtain ⟨n,hn⟩ := six_dvd_cubic_order p (by have := hp.two_le; omega)
  refine ⟨n,?_⟩
  omega

theorem prime_model_three_rank_pos {Q : Type*} [Group Q] [Finite Q]
    {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p) (e : Q ≃* PSL(2,F)) : 1 ≤ primeRank 3 Q := by
  have hn : primeRank 3 Q ≠ 0 := fun hz =>
    PrimeRank.eq_zero_iff_not_dvd_card.mp hz (prime_model_three_dvd_card hp ho hF e)
  omega
end Theory.PSL2
