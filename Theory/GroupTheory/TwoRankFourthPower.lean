module

public import Theory.GroupTheory.PrimeRankAutomorphismOrder
public import Theory.GroupTheory.PrimeRankZero

/-!
# Two-rank bounds from fourth powers and odd outer quotients

A group of order 2^(n+2) with a nontrivial fourth power has no elementary
subgroup of index one or two, hence has two-rank at most n. An odd outer
automorphism quotient adds no two-rank to a centerless finite group.
These are elementary subgroup/quotient arguments used by the q=2 triality
consumer of Aschbacher–Smith G.9.3, printed p.356.
-/

public section
namespace Theory.GroupTheory
open Subgroup

/-- A fourth-power witness rules out elementary subgroups of index one or two. -/
theorem twoRank_le_of_card_pow_and_fourth_ne
    {G : Type*} [Group G] [Finite G] (n : ℕ)
    (hcard : Nat.card G = 2 ^ (n + 2)) (x : G) (hx : x ^ 4 ≠ 1) :
    primeRank 2 G ≤ n := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro E hE
  let := hE
  obtain ⟨a, ha⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hale : a ≤ n + 2 := by
    have hc := Subgroup.card_le_card_group E
    rw [ha, hcard] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  suffices a ≤ n by
    rw [ha]
    exact Nat.pow_le_pow_right (by decide) this
  by_contra h
  have cases : a = n + 1 ∨ a = n + 2 := by omega
  have hsq (y : G) (hy : y ∈ E) : y ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian y hy
  rcases cases with rfl | rfl
  · have hi : E.index = 2 := by
      have hm := E.card_mul_index
      rw [ha, hcard, show n + 2 = (n + 1) + 1 by omega, pow_succ] at hm
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (n + 1)) hm
    have hs := hsq (x ^ 2) (E.sq_mem_of_index_two hi x)
    exact hx (by simpa only [← pow_mul] using hs)
  · have ht : E = ⊤ := E.eq_top_of_card_eq (ha.trans hcard.symm)
    have hs := hsq x (ht ▸ mem_top x)
    apply hx
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs, one_pow]

/-- An odd outer quotient adds no two-rank to a centerless group. -/
theorem automorphism_twoRank_le_of_odd_outer
    {S : Type*} [Group S] [Finite S] (hz : center S = ⊥)
    (hodd : ¬ 2 ∣ Nat.card (MulAut.Outer S)) :
    primeRank 2 (MulAut S) ≤ primeRank 2 S := by
  have hf : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply (MulAut.conj : S →* MulAut S).ker.eq_bot_iff_forall.mpr
    intro x hx
    have hx' : MulAut.conj x = 1 := hx
    have hc : x ∈ center S := by
      rw [mem_center_iff]
      intro y
      have hy := MulEquiv.congr_fun hx' y
      change x * y * x⁻¹ = y at hy
      exact (mul_inv_eq_iff_eq_mul.mp hy).symm
    simpa only [hz, mem_bot] using hc
  let e : S ≃* MulAut.innerSubgroup S := MonoidHom.ofInjective hf
  have hr := primeRank_le_ker_add
    (QuotientGroup.mk' (MulAut.innerSubgroup S)) (p := 2)
  rw [QuotientGroup.ker_mk', ← primeRank_equiv 2 e] at hr
  change primeRank 2 (MulAut S) ≤
    primeRank 2 S + primeRank 2 (MulAut.Outer S) at hr
  rw [(PrimeRank.eq_zero_iff_not_dvd_card).mpr hodd, Nat.add_zero] at hr
  exact hr

end Theory.GroupTheory
