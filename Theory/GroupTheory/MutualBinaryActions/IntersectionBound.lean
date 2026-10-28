module

public import Theory.GroupTheory.MutualBinaryActions
public import Mathlib.Tactic.Linarith

/-!
# Commutators of abelian subgroups with a large intersection

If two abelian subgroups normalize one another and each has order at most
 twice the order of their intersection, their commutator has order at most
two. The intersection centralizes both subgroups, so both conjugation images
have order at most two. The mutual-action bound then applies.

The second formulation restricts the groups to a common finite subgroup
and transports the commutator back to the original ambient group.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
the commutator argument preceding (6.12.3), printed p.404.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

private theorem intersection_relIndex_le_two [Finite G]
    (A B : Subgroup G) (hB : Nat.card B ≤ 2 * Nat.card (A ⊓ B : Subgroup G)) :
    (A ⊓ B).relIndex B ≤ 2 := by
  have he := ((A ⊓ B).subgroupOf B).card_mul_index
  have hc : Nat.card ((A ⊓ B).subgroupOf B) = Nat.card (A ⊓ B : Subgroup G) :=
    Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ B ≤ B from inf_le_right)).toEquiv
  rw [hc] at he
  change Nat.card (A ⊓ B : Subgroup G) * (A ⊓ B).relIndex B = Nat.card B at he
  have hp : 0 < Nat.card (A ⊓ B : Subgroup G) := Nat.card_pos
  nlinarith

theorem commutator_card_le_two_of_large_abelian_intersection [Finite G]
    (A B : Subgroup G) [IsMulCommutative A] [IsMulCommutative B]
    (hBA : B ≤ normalizer (A : Set G)) (hAB : A ≤ normalizer (B : Set G))
    (hA : Nat.card A ≤ 2 * Nat.card (A ⊓ B : Subgroup G))
    (hB : Nat.card B ≤ 2 * Nat.card (A ⊓ B : Subgroup G)) :
    Nat.card (⁅A, B⁆ : Subgroup G) ≤ 2 := by
  apply commutator_card_le_two_of_mutual_centralizer_indices A B hBA hAB
  · exact (relIndex_le_of_le_left
      (show A ⊓ B ≤ centralizer (A : Set G) from inf_le_left.trans (le_centralizer A))
      (index_ne_zero_of_finite (H := (A ⊓ B).subgroupOf B))).trans
      (intersection_relIndex_le_two A B hB)
  · have hidx : (B ⊓ A).relIndex A ≤ 2 :=
      intersection_relIndex_le_two B A (by simpa only [inf_comm] using hA)
    exact (relIndex_le_of_le_left
      (show B ⊓ A ≤ centralizer (B : Set G) from inf_le_left.trans (le_centralizer B))
      (index_ne_zero_of_finite (H := (B ⊓ A).subgroupOf A))).trans hidx

theorem commutator_card_le_two_of_large_abelian_intersection_in_finite_subgroup
    (A B K : Subgroup G) [Finite K] [IsMulCommutative A] [IsMulCommutative B]
    (hAK : A ≤ K) (hBK : B ≤ K)
    (hBA : B ≤ normalizer (A : Set G)) (hAB : A ≤ normalizer (B : Set G))
    (hA : Nat.card A ≤ 2 * Nat.card (A ⊓ B : Subgroup G))
    (hB : Nat.card B ≤ 2 * Nat.card (A ⊓ B : Subgroup G)) :
    Nat.card (⁅A, B⁆ : Subgroup G) ≤ 2 := by
  have hcA : Nat.card (A.subgroupOf K) = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv
  have hcB : Nat.card (B.subgroupOf K) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv
  have hcI : Nat.card (A.subgroupOf K ⊓ B.subgroupOf K : Subgroup K) =
      Nat.card (A ⊓ B : Subgroup G) :=
    Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ B ≤ K from inf_le_left.trans hAK)).toEquiv
  have hm : ⁅A.subgroupOf K, B.subgroupOf K⁆.map K.subtype = ⁅A, B⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le hAK, map_subgroupOf_eq_of_le hBK]
  rw [← hm, card_map_of_injective K.subtype_injective]
  apply commutator_card_le_two_of_large_abelian_intersection (A.subgroupOf K) (B.subgroupOf K)
  · rw [← subgroupOf_normalizer_eq hAK]
    exact fun _ hb => hBA hb
  · rw [← subgroupOf_normalizer_eq hBK]
    exact fun _ ha => hAB ha
  · simpa only [hcA, hcI] using hA
  · simpa only [hcB, hcI] using hB
end Subgroup
