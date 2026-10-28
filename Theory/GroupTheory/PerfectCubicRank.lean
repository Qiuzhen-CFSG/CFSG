module
public import Theory.GroupTheory.PerfectCenterPrimeRank
public import Theory.GroupTheory.PrimeRankInvolutionLift
/-!
# Rank at a cubic Sylow prime in a perfect centered group

A p-group center of a perfect group lies in the commutator of every Sylow
p-subgroup. If p⁴ does not divide the group order, an elementary subgroup
of rank at least three would itself be a Sylow subgroup and would force
that center to be trivial. Thus the p-rank is at most two.

Source: central Sylow transfer, used for the triple A₆ and A₇ cases of
Aschbacher–Smith A.2.12(I), printed p.36.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
variable {p : ℕ} [Fact p.Prime]

theorem primeRank_le_two_of_center_of_fourth_power_not_dvd
    (hZ : IsPGroup p (center G)) (hZne : center G ≠ ⊥)
    (hcard : ¬ p ^ 4 ∣ Nat.card G) : primeRank p G ≤ 2 := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro E hE
  let := hE
  have hEp := IsElementaryAbelian.isPGroup p E
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hn3 : n ≤ 3 := by
    by_contra hh
    apply hcard
    exact (pow_dvd_pow p (by omega : 4 ≤ n)).trans
      (hn ▸ (P : Subgroup G).card_subgroup_dvd_card)
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hkn : k ≤ n := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    exact hk ▸ hn ▸ card_le_of_le hEP
  have hk2 : k ≤ 2 := by
    by_contra hh
    have hk3 : k = 3 := by omega
    have hn3 : n = 3 := by omega
    have heq : E = (P : Subgroup G) := eq_of_le_of_card_ge hEP (by rw [hk, hn, hk3, hn3])
    have hzP : center G ≤ (P : Subgroup G) := hZ.le_sylow_of_normal P
    have hzcomm : center G ≤ ⁅(P : Subgroup G), (P : Subgroup G)⁆ := by
      intro z hz
      apply center_inf_commutator_inf_sylow_le_commutator P
      exact ⟨⟨hz, Group.IsPerfect.commutator_eq_top (G := G) ▸ mem_top z⟩, hzP hz⟩
    have hc : ⁅E,E⁆ = ⊥ := by
      rw [← map_subtype_commutator, commutator_eq_bot, Subgroup.map_bot]
    rw [← heq, hc] at hzcomm
    exact hZne (le_bot_iff.mp hzcomm)
  rw [hk]
  exact pow_le_pow_right' (Fact.out : p.Prime).one_lt.le hk2

end Theory.GroupTheory
