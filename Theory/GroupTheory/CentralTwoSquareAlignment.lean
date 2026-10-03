module
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.PGroup

/-!
# Matching exterior squares by odd powers

Let b lie outside a subgroup N, with its square generating a nontrivial
two-subgroup C contained in N. Every generator c of C is the square of
an odd power of b which still lies outside N. The ambient group is finite;
normality, index two and centrality are not needed for this power argument.

Write c=(b²)^k. Equal generator orders imply that k is odd: if it were
even, the gcd in the order-of-a-power formula would be at least two and
would strictly lower the order. Writing k=2l+1, membership of b^k in N
would imply membership of b by multiplication with (b²)^(-l).

This is the square-alignment step in Alperin--Brauer--Gorenstein II.3
Proposition 3, article p26. It matches the model's exterior square with
the image of the source square under the already chosen central-layer
equivalence, before comparing the actual index-two extensions.
-/

namespace Subgroup

public theorem exists_exterior_pow_square_eq_generator
    {G : Type*} [Group G] [Finite G] (N C : Subgroup G)
    (hCN : C ≤ N) (hC : C ≠ ⊥) (hC2 : IsPGroup 2 C)
    (b c : G) (hb : b ∉ N) (hbsq : Subgroup.zpowers (b ^ 2) = C)
    (hc : Subgroup.zpowers c = C) :
    ∃ k : ℕ, Odd k ∧ b ^ k ∉ N ∧ (b ^ k) ^ 2 = c := by
  have hcC : c ∈ C := hc ▸ Subgroup.mem_zpowers c
  have hcPow : c ∈ Submonoid.powers (b ^ 2) := by
    rw [mem_powers_iff_mem_zpowers, hbsq]
    exact hcC
  obtain ⟨k, hk⟩ := hcPow
  change (b ^ 2) ^ k = c at hk
  have hord : orderOf c = orderOf (b ^ 2) := by
    rw [← Nat.card_zpowers, ← Nat.card_zpowers, hc, hbsq]
  have hcard : orderOf (b ^ 2) = Nat.card C := by rw [← Nat.card_zpowers, hbsq]
  have hne : Nat.card C ≠ 1 := by exact fun h => hC (Subgroup.card_eq_one.mp h)
  have htwo : 2 ∣ Nat.card C := hC2.card_eq_or_dvd.resolve_left hne
  have hodd : Odd k := by
    by_contra hko
    have hkEven : 2 ∣ k := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hko)
    have horder : orderOf (b ^ 2) / (orderOf (b ^ 2)).gcd k = orderOf (b ^ 2) := by
      rw [← orderOf_pow, hk, hord]
    have hpos : 0 < orderOf (b ^ 2) := orderOf_pos _
    have hge : 2 ≤ (orderOf (b ^ 2)).gcd k := Nat.le_of_dvd
      (Nat.gcd_pos_of_pos_left k hpos) (Nat.dvd_gcd (hcard ▸ htwo) hkEven)
    have hlt := Nat.div_lt_self hpos hge
    omega
  refine ⟨k, hodd, ?_, ?_⟩
  · intro hbk
    obtain ⟨l, hl⟩ := hodd
    have hpow : (b ^ 2) ^ l * b = b ^ k := by rw [hl, pow_add, pow_mul, pow_one]
    have hs : b ^ 2 ∈ N := hCN (hbsq ▸ Subgroup.mem_zpowers _)
    have h := N.mul_mem (N.inv_mem (N.pow_mem hs l)) hbk
    rw [← hpow, inv_mul_cancel_left] at h
    exact hb h
  · rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    exact hk

end Subgroup

