module
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero
/-!
# Three commuting contributions to prime rank

Two commuting factors with centers prime to p contribute their p-ranks
independently of a third common centralizer. Applying the two-factor rank
inequality first inside a join and then in the ambient group gives rank
at least three when all three orders are divisible by p. The factors need
not be isomorphic and may have nontrivial central intersections.

Source: Aschbacher–Smith, the odd-rank contradiction in 14.6.9, printed p. 1026.
-/
public section
namespace Theory.GroupTheory
open Subgroup ResidualCentralizerRank
variable {G : Type*} [Group G] [Finite G]

private theorem rank_add_le_join {p : ℕ} [Fact p.Prime]
    (A B : Subgroup G) (hc : A ≤ centralizer (B : Set G))
    (hz : Nat.Coprime p (Nat.card (center B))) :
    primeRank p A + primeRank p B ≤ primeRank p (A ⊔ B : Subgroup G) := by
  let J := A ⊔ B
  let eA := subgroupOfEquivOfLe (show A ≤ J from le_sup_left)
  let eB := subgroupOfEquivOfLe (show B ≤ J from le_sup_right)
  have hz' : Nat.Coprime p (Nat.card (center (B.subgroupOf J))) := by
    rwa [Nat.card_congr (centerCongr eB).toEquiv]
  have hr := primeRank_add_le_of_center_coprime (A.subgroupOf J) (B.subgroupOf J)
    (show A.subgroupOf J ≤ centralizer (B.subgroupOf J : Set J) from
      fun a ha b hb => Subtype.ext (hc ha b hb)) hz'
  rwa [primeRank_equiv p eA,primeRank_equiv p eB] at hr

/-- Three commuting factors give rank three when two factor centers are prime to p. -/
theorem primeRank_three_of_commuting_of_centers_coprime
    {p : ℕ} [Fact p.Prime] (P Q A : Subgroup G)
    (hPQ : P ≤ centralizer (Q : Set G))
    (hAP : A ≤ centralizer (P : Set G)) (hAQ : A ≤ centralizer (Q : Set G))
    (hP : Nat.Coprime p (Nat.card (center P)))
    (hQ : Nat.Coprime p (Nat.card (center Q)))
    (hdP : p ∣ Nat.card P) (hdQ : p ∣ Nat.card Q) (hdA : p ∣ Nat.card A) :
    3 ≤ primeRank p G := by
  have h1 := rank_add_le_join A P hAP hP
  have h2 := primeRank_add_le_of_center_coprime (A ⊔ P) Q (sup_le hAQ hPQ) hQ
  have hr (B : Subgroup G) (hd : p ∣ Nat.card B) : 1 ≤ primeRank p B := by
    by_contra! hh
    exact (PrimeRank.eq_zero_iff_not_dvd_card.mp (by omega : primeRank p B = 0)) hd
  have := hr P hdP
  have := hr Q hdQ
  have := hr A hdA
  omega
end Theory.GroupTheory
