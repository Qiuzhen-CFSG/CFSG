module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.Reduction
public import Theory.GroupTheory.SolvableSmallOddCore
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# The nontrivial two-core of the actual odd-prime Sylow product

The permuting product has two-prime order and is solvable. Its odd core has
order bounded by the original odd complement, while its full two-subgroup
retains its order. Explicit GL(n,p) orders then force a nontrivial two-core.

Source: Aschbacher–Smith, Proposition 1.3.4, printed pp.510–511,
using the original full Sylow hypothesis in A.3.15.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
variable {G : Type*} [Group G] [Finite G]

theorem product_twoCore_ne_bot {p d t : ℕ} [Fact p.Prime]
    (B S : Subgroup G) (hB : IsPGroup p B) (hS : IsPGroup 2 S)
    (hp : p ≠ 2) (hperm : (B : Set G) * S = (S : Set G) * B)
    (hcard : Nat.card B ≤ p ^ d) (hdiv : 2 ^ t ∣ Nat.card S)
    (hnum : ∀ n ≤ d, ¬ 2 ^ t ∣ ∏ i : Fin n, (p ^ n - p ^ (i : ℕ))) :
    pCore 2 (B ⊔ S : Subgroup G) ≠ ⊥ := by
  let H := B ⊔ S
  have hd := IsPGroup.disjoint_of_ne p 2 hp B S hB hS
  have hc := card_set_mul_mul_card_inf B S
  rw [hd.eq_bot, card_bot, mul_one, ← coe_sup_of_set_mul_comm B S hperm] at hc
  change Nat.card H = Nat.card B * Nat.card S at hc
  apply twoCore_ne_bot_of_solvable_small_odd_core hp
    (solvable_product B S hB hS hp hperm)
  · intro q hq hqG
    rw [hc] at hqG
    rcases hq.dvd_mul.mp hqG with hb | hs
    · obtain ⟨n, hn⟩ := hB.exists_card_eq
      rw [hn] at hb
      exact Or.inr ((Nat.dvd_prime (Fact.out : p.Prime)).mp
        (hq.dvd_of_dvd_pow hb) |>.resolve_left hq.ne_one)
    · obtain ⟨n, hn⟩ := hS.exists_card_eq
      rw [hn] at hs
      exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
        (hq.dvd_of_dvd_pow hs) |>.resolve_left hq.ne_one)
  · have hcop : Nat.Coprime (Nat.card (pCore p H)) (Nat.card S) :=
      IsPGroup.coprime_card_of_ne p 2 hp _ _ pCore_isPGroup hS
    have hnd : Nat.card (pCore p H) ∣ Nat.card B := by
      apply hcop.dvd_of_dvd_mul_right
      rw [← hc]
      exact (pCore p H).card_subgroup_dvd_card
    exact (Nat.le_of_dvd Nat.card_pos hnd).trans hcard
  · exact hdiv.trans (card_dvd_of_le (show S ≤ H from le_sup_right))
  · exact hnum

theorem product_twoCore_ne_bot_of_exceptional_prime {p : ℕ} [Fact p.Prime]
    (hp : p = 5 ∨ p = 7 ∨ p = 11)
    (B S : Subgroup G) (hB : XiOddQuotient p B) (hS : IsPGroup 2 S)
    (hperm : (B : Set G) * S = (S : Set G) * B)
    (hdiv : 256 ∣ Nat.card S) : pCore 2 (B ⊔ S : Subgroup G) ≠ ⊥ := by
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl | rfl <;> decide
  have hcard : Nat.card B ≤ p ^ 3 := by
    rcases hB with ⟨_,hc⟩ | ⟨_,hc,_⟩
    · rw [hc]
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by decide)
    · exact hc.le
  apply product_twoCore_ne_bot (d := 3) (t := 8) B S hB.isPGroup hS hp2 hperm hcard hdiv
  intro n hn
  rcases hp with rfl | rfl | rfl <;> interval_cases n <;> norm_num [Fin.prod_univ_succ]
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
