module
public import Theory.GroupAction.FourTwoActionLine
public import Theory.GroupTheory.SubgroupConjugation
/-!
# Displacement of a four-group under a two-group

A two-group normalizing a group of order four fixes its commutator subgroup
pointwise. If that commutator subgroup is nontrivial, it has order two.
These are the ambient-subgroup forms of the fixed-point and displacement
calculations in `FourElementTwoAction` and `FourTwoActionLine`; the proof
uses the literal conjugation action and then maps through the inclusion.

The MS93 original-group application is in `DistanceEight.OriginalDisplacement`.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] (H P : Subgroup G)
  (hn : P ≤ normalizer (H : Set G)) (hp : IsPGroup 2 P) [Finite H]
  (hfour : Nat.card H = 4)

include hn hp hfour in
/-- A two-group fixes the displacement of every normalized four-group. -/
theorem commutator_four_le_centralizer : ⁅H,P⁆ ≤ centralizer (P : Set G) := by
  let _ : Normalizes P H := ⟨hn⟩
  have hquad := two_group_action_on_four_is_quadratic (V := H) hp hfour
  have hfix := commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hquad
  rw [← commutatorAction_subgroup_conj_map_eq_commutator H P hn]
  rintro x ⟨y,hy,rfl⟩ p hp
  have he := congrArg Subtype.val (hfix hy ⟨p,hp⟩)
  change p * (y : G) * p⁻¹ = y at he
  exact mul_inv_eq_iff_eq_mul.mp he

include hn hp hfour in
/-- Nontrivial displacement of a normalized four-group has order two. -/
theorem commutator_four_card_of_ne_bot (hne : ⁅H,P⁆ ≠ ⊥) :
    Nat.card (⁅H,P⁆ : Subgroup G) = 2 := by
  let _ : Normalizes P H := ⟨hn⟩
  have hmap := commutatorAction_subgroup_conj_map_eq_commutator H P hn
  have hne' : commutatorAction P H ≠ ⊥ := by
    intro he
    apply hne
    rw [← hmap,he,Subgroup.map_bot]
  rw [← hmap,card_map_of_injective H.subtype_injective]
  exact commutatorAction_card_two_of_nontrivial_two_action_on_four hp hfour hne'
end Subgroup
