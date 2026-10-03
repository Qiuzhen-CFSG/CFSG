module

public import Theory.GroupTheory.PGroup.RankTwoNormalFour
public import Theory.GroupTheory.InvolutionTransfer

/-!
# Involution fusion into a normal four-group

Suppose a Sylow two-subgroup has just one central involution and contains
an elementary normal four-group. Under the elementary rank bound of two,
every ambient involution class meeting the Sylow meets that four-group,
provided the ambient group has no normal subgroup of index two.

The centralizer of the four-group has index two. Thompson transfer moves
an involution into this centralizer, and the elementary rank bound puts the
resulting involution in the four-group itself.

This is a rank-two reduction for the involution-fusion cases in
Janko–Thompson, Math. Z. 113 (1970), §§3 and 6, especially p.395.
-/

namespace Sylow

open Subgroup

/-- Every Sylow involution has an ambient conjugate in the normal four-group. -/
public theorem exists_isConj_mem_normal_four_of_elementary_card_lt_eight
    {G : Type*} [Group G] [Finite G]
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) (t : S) (ht : orderOf t = 2) :
    ∃ u : S, u ∈ E ∧ IsConj (t : G) (u : G) := by
  have hindex := centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
    S.isPGroup' hZ E hE
  obtain ⟨u, htu, hu⟩ := S.exists_isConj_mem_of_index_two hno
    (centralizer (E : Set S)) hindex t ht
  have ht2 : (t : G) ^ 2 = 1 := by
    exact congrArg Subtype.val (show t ^ 2 = 1 by simpa only [ht] using pow_orderOf_eq_one t)
  have hu2 : u ^ 2 = 1 := by
    apply Subtype.ext
    have h := htu.pow 2
    rw [ht2] at h
    exact isConj_one_right.mp h
  exact ⟨u, mem_four_of_square_eq_one_of_elementary_card_lt_eight
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) E hE hu2 hu, htu⟩

end Sylow
