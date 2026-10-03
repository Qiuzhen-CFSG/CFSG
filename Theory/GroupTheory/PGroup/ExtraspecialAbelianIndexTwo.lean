module

public import Theory.GroupTheory.PGroup.ExtraspecialInvolution
public import Theory.GroupTheory.Commutator.BoundedImageKernel

/-!
# Abelian index-two subgroups of extraspecial two-groups

An abelian subgroup of index two in an extraspecial two-group has order at
most four. The commutator with an element outside it has image in the center
of order two and kernel in that center. Thus extraspecial groups of order
larger than eight have no such abelian subgroup.

This elementary commutator-kernel argument supplies the centralizer
noncommutativity needed in Janko–Thompson, Math. Z. 113 (1970), §4, p.389.
-/

open Subgroup
open scoped commutatorElement

namespace IsExtraspecial

/-- An extraspecial two-group of order greater than eight has no abelian
subgroup of index two. -/
public theorem not_isMulCommutative_of_index_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hP : 8 < Nat.card P) (A : Subgroup P) (hi : A.index = 2)
    (hZA : center P ≤ A) : ¬ IsMulCommutative A := by
  intro hab
  have hclass := (quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient
  obtain ⟨K, _, hcard, hK⟩ := exists_large_subgroup_commutator_le_of_index_two
    A A ⊤ A ⊥ (center P) le_rfl hab hZA
    ((commutator_mono le_top le_rfl).trans hclass)
    le_top (le_centralizer_iff_isMulCommutative.mpr hab)
    (by simpa using hi)
  have hKZ : K ≤ center P := commutator_top_right_eq_bot_iff_le_center.mp
    (bot_unique hK)
  have hbound := card_le_of_le hKZ
  rw [center_order_p 2 P] at hbound
  have htwo : (⊥ : Subgroup P).relIndex (center P) = 2 := by
    simp only [relIndex, bot_subgroupOf, index_bot, center_order_p 2 P]
  rw [htwo] at hcard
  have hc := A.card_mul_index
  rw [hi] at hc
  omega

end IsExtraspecial
