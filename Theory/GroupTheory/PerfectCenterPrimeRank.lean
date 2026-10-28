module
public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Mathlib.GroupTheory.IsPerfect

/-!
# Odd rank forced by a nontrivial prime-group center

If the odd prime rank were at most one, the Sylow subgroup would be cyclic.
Central transfer places the center of a perfect group in that Sylow's
commutator subgroup, a contradiction. This avoids any model classification.

Source: Aschbacher–Smith A.2.12(I), printed p.36, and central Sylow transfer.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
variable {p : ℕ} [Fact p.Prime]
theorem two_le_primeRank_of_nontrivial_prime_center
    (hp : Odd p) (hZ : IsPGroup p (center G)) (hne : center G ≠ ⊥) :
    2 ≤ primeRank p G := by
  by_contra hr
  let P : Sylow p G := Classical.choice inferInstance
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one hp (by omega)
  have hzP : center G ≤ (P : Subgroup G) := hZ.le_sylow_of_normal P
  have hzc : center G ≤ ⁅(P : Subgroup G), (P : Subgroup G)⁆ := by
    intro z hz
    apply center_inf_commutator_inf_sylow_le_commutator P
    exact ⟨⟨hz, (Group.IsPerfect.commutator_eq_top (G := G)) ▸ mem_top z⟩, hzP hz⟩
  have hc : ⁅(P : Subgroup G), (P : Subgroup G)⁆ = ⊥ := by
    rw [← map_subtype_commutator, commutator_eq_bot, Subgroup.map_bot]
  exact hne (le_bot_iff.mp (hc ▸ hzc))
end Theory.GroupTheory
