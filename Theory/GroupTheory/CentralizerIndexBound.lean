module

public import Mathlib.GroupTheory.Index

/-!
# Bounding a subgroup by a centralizer and a relative index

If X centralizes a set U, then X ∩ B lies in C_B(U). Counting X by
this intersection bounds its order by |C_B(U)| times |X : X ∩ B|.
This is the elementary subgroup index formula.
-/

namespace Subgroup

/-- Count a subgroup centralizing a set through its intersection with B. -/
public theorem card_le_centralizer_card_mul_relIndex
    {G : Type*} [Group G] [Finite G] (X B : Subgroup G) (U : Set G)
    (hX : X ≤ centralizer U) :
    Nat.card X ≤ Nat.card ((centralizer U).subgroupOf B) * B.relIndex X := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (B ⊓ X) X bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_right] at hc
  let i : (B ⊓ X : Subgroup G) → (centralizer U).subgroupOf B :=
    fun x => ⟨⟨x, x.property.1⟩, hX x.property.2⟩
  have hi : Function.Injective i := by
    intro x y heq
    exact Subtype.ext (congrArg (fun a : (centralizer U).subgroupOf B => ((a : B) : G)) heq)
  rw [← hc]
  exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective i hi)

end Subgroup
