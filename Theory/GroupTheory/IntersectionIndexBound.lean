module
public import Mathlib.GroupTheory.Index

/-!
# Counting a subgroup through an intersection

For V contained in K, its cosets modulo C intersect V inject into the
cosets of C intersect K in K. Multiplying by |C intersect V| gives
|V| <= |C intersect V| [K : C intersect K], without a normality assumption.

The source consumer is the middle-root index estimate in Fong--Seitz I
(6F), printed p.47.
-/

namespace Subgroup
public theorem card_le_card_inf_mul_relIndex_of_le {G : Type*} [Group G] [Finite G]
    (V C K : Subgroup G) (hVK : V ≤ K) :
    Nat.card V ≤ Nat.card ↥(C ⊓ V) * C.relIndex K := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (C ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right] at hc
  rw [←hc]
  exact Nat.mul_le_mul_left _ (relIndex_le_of_le_right hVK
    (show C.relIndex K ≠ 0 from Nat.ne_of_gt Nat.card_pos))
end Subgroup
