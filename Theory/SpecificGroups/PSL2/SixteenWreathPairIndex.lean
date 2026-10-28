module
public import Theory.SpecificGroups.PSL2.SixteenWreathOrder
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The outer index of the actual PSL₂(16) component pair

Every C-component of the full automorphism wreath model is PSL₂(16).
Two distinct such components commute and intersect trivially; their
product has order 4080² and index 32. This calculation concerns the
literal components, so it transports through the original Mc/O₂(Mc)
model without choosing new factor embeddings.

The Chapter14 consumer applies the index to the image of K_z and
compares its Sylow-two quotient with the original exchanged actor.
Source: Aschbacher--Smith 14.6.14(4)--15, printed pp.1033--1034.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.PSL2.SixteenWreathComponents

/-- The two distinct actual components form a direct product of order 4080². -/
theorem component_pair_card {A B : Subgroup W}
    (hA : A.IsCComponent) (hB : B.IsCComponent) (hne : A ≠ B) :
    Nat.card (A ⊔ B : Subgroup W) = 4080^2 := by
  obtain ⟨eA⟩ := component_equiv hA
  obtain ⟨eB⟩ := component_equiv hB
  let := simple
  let : IsSimpleGroup A := eA.isSimpleGroup
  let : IsSimpleGroup B := eB.isSimpleGroup
  let := hA.perfect
  have hc : A ≤ centralizer (B : Set W) := commutator_eq_bot_iff_le_centralizer.mp
    (simple_subnormal_commute_of_ne A B hA.subnormal hB.subnormal hne)
  have hz : center A = ⊥ :=
    (inferInstance : (center A).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp he))
  have hd : Disjoint A B := by
    apply disjoint_def.mpr
    intro x hx hy
    have hh : (⟨x,hx⟩ : A) ∈ center A := mem_center_iff.mpr fun y =>
      Subtype.ext ((hc y.property x hy).symm)
    exact congrArg Subtype.val (show (⟨x,hx⟩ : A) = 1 from mem_bot.mp (hz ▸ hh))
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  rw [←Nat.card_congr e.toEquiv,Nat.card_prod,
    Nat.card_congr eA.toEquiv,Nat.card_congr eB.toEquiv,model_card]
  rfl

/-- The actual component product has outer index 32 in the full wreath model. -/
theorem component_pair_index {A B : Subgroup W}
    (hA : A.IsCComponent) (hB : B.IsCComponent) (hne : A ≠ B) :
    (A ⊔ B).index = 32 := by
  have hh := (A ⊔ B).card_mul_index
  rw [component_pair_card hA hB hne,wreath_card] at hh
  omega

/-- A normal component pair has a two-group quotient of order 32. -/
theorem component_pair_quotient_isTwoGroup {A B : Subgroup W}
    (hA : A.IsCComponent) (hB : B.IsCComponent) (hne : A ≠ B)
    [(A ⊔ B).Normal] : IsPGroup 2 (W ⧸ (A ⊔ B)) := by
  apply IsPGroup.of_card (n := 5)
  rw [←index_eq_card,component_pair_index hA hB hne]
  rfl
end Theory.PSL2.SixteenWreathComponents
