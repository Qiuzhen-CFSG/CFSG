module
public import Theory.GroupTheory.ElementaryCommutingTwoGroup
public import Theory.ElementaryAbelian.Join

/-!
# Nonisolated four-groups in a two-subgroup

A four-group in a finite two-subgroup that commutes with a distinct
four-group belongs to the component of every elementary subgroup of order
at least eight. The commuting four-groups have elementary join of order at
least eight, so the rank-three connectivity theorem applies.

This is the nonisolated-vertex step of GLS2, Lemma 10.21 and Section 22
(`refs/KGroup/GLS2/ChapterC.tex`, `refs/KGroup/GLS2/ChapterF.tex`). All paths
are in the actual ambient elementary commuting relation.
-/

namespace Subgroup

/-- The join of two distinct subgroups of order four has order at least eight. -/
public theorem eight_le_card_sup_of_distinct_four
    {G : Type*} [Group G] [Finite G] (V W : Subgroup G)
    (hV : Nat.card V = 4) (hW : Nat.card W = 4) (hne : W ≠ V) :
    8 ≤ Nat.card (V ⊔ W : Subgroup G) := by
  have hgt : 4 < Nat.card (V ⊔ W : Subgroup G) := by
    by_contra h
    have heq : V = V ⊔ W := eq_of_le_of_card_ge le_sup_left (by omega)
    have hWV : W ≤ V := heq ▸ le_sup_right
    exact hne (eq_of_le_of_card_ge hWV (by omega))
  have hdiv := card_dvd_of_le (show V ≤ V ⊔ W from le_sup_left)
  rw [hV] at hdiv
  obtain ⟨k, hk⟩ := hdiv
  omega

/-- A nonisolated four-group in a two-subgroup is connected to each
rank-three elementary subgroup of that two-subgroup. -/
public theorem elementaryCommutingConnected_of_distinct_commuting_four
    {G : Type*} [Group G] [Finite G] (S A V W : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4) (hW : Nat.card W = 4)
    (hAS : A ≤ S) (hVS : V ≤ S) (hWS : W ≤ S)
    (hcomm : W ≤ centralizer (V : Set G)) (hne : W ≠ V) :
    ElementaryCommutingConnected 2 A V := by
  let : IsElementaryAbelian 2 (V ⊔ W : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hcomm
  have h8 := eight_le_card_sup_of_distinct_four V W hV hW hne
  apply (elementaryCommutingConnected_of_le_twoGroup S A (V ⊔ W) hS
    hA h8 hAS (sup_le hVS hWS)).trans
  apply ElementaryCommutingAdjacent.connected
  refine ⟨inferInstance, by omega, inferInstance, by omega, ?_⟩
  intro x hx v hv
  exact congrArg Subtype.val
    ((IsMulCommutative.is_comm (M := (V ⊔ W : Subgroup G))).comm
      ⟨v, (show V ≤ V ⊔ W from le_sup_left) hv⟩ ⟨x, hx⟩)

end Subgroup
