module
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

open Subgroup

/-!
# Faithful two-actors on three-groups of rank at most one

An odd prime group of prime rank at most one is cyclic. Its automorphism
group has Euler-totient order, whose two-part is at most two when the prime
is three. Thus a faithfully acting group of order `2^m` has `m ≤ 1`.
This is the rank-one case needed after the independent actor-rank bound
in the cubic branch of Aschbacher--Smith G.9.4, printed p.355.
-/

namespace Theory.GroupTheory

/-- A faithful two-actor on a three-group of rank at most one has rank at most one. -/
public theorem faithful_two_actor_rank_le_one_of_three_rank_le_one
    {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) [B.Normal] (hB : IsPGroup 3 B)
    {m : ℕ} (hA : Nat.card A = 2 ^ m)
    (hf : A ⊓ centralizer (B : Set G) = ⊥)
    (hr : primeRank 3 B ≤ 1) : m ≤ 1 := by
  let : IsCyclic B := hB.isCyclic_of_odd_of_elementary_card_le (by decide)
    (fun E hE => by
      let : IsElementaryAbelian 3 E := hE
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr E)
  let f : A →* MulAut B := MulAut.conjNormal.comp A.subtype
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro a ha
    have hc : (a : G) ∈ centralizer (B : Set G) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer]
      exact ha
    exact Subtype.ext (hf.le ⟨a.property, hc⟩)
  have hd := Subgroup.card_dvd_of_injective f hfi
  rw [hA, IsCyclic.card_mulAut] at hd
  obtain ⟨n, hn⟩ := hB.exists_card_eq
  rw [hn] at hd
  by_cases hn0 : n = 0
  · subst n
    norm_num at hd
    omega
  · rw [Nat.totient_prime_pow Nat.prime_three (Nat.pos_of_ne_zero hn0)] at hd
    norm_num at hd
    rw [mul_comm] at hd
    by_contra hm
    have h4 : 4 ∣ 2 ^ m := pow_dvd_pow 2 (by omega : 2 ≤ m)
    have h2 : 2 ∣ 3 ^ (n - 1) := by
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp (h4.trans hd)
    have ho : Odd (3 ^ (n - 1)) := (by decide : Odd 3).pow
    exact ho.not_two_dvd_nat h2

end Theory.GroupTheory
