module
public import Theory.GroupTheory.SmallMoverEqualOrder

/-!
# Kernel containment from equal orders and quotient indices

If two finite subgroups have equal order, the one containing the kernel
has the smaller quotient image. Equality of those image orders forces the
other subgroup to contain the whole kernel as well. Matching upper and
lower bounds are a useful form of this saturation argument.

The literal unequal-neighbor application is in
NonbinarySymplectic.CriticalReduction.UnequalBranches, for the kernel
clause of MS93 (5.5)(c), printed p.915.
-/

public section
open Subgroup
namespace Subgroup.SmallMover
variable {G : Type*} [Group G] [Finite G]

/-- Equal image orders force the entire kernel into the equal-order competitor. -/
theorem kernel_le_of_card_eq_of_relIndex_eq (Q J E : Subgroup G) (hQJ : Q ≤ J)
    (hc : Nat.card J = Nat.card E) (hi : Q.relIndex J = Q.relIndex E) : Q ≤ E := by
  have hj := relIndex_mul_relIndex (⊥ : Subgroup G) Q J bot_le hQJ
  rw [relIndex_bot_left,relIndex_bot_left,hc,hi] at hj
  have he := relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ E) E bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right] at he
  have hcard : Nat.card Q = Nat.card (Q ⊓ E : Subgroup G) :=
    Nat.eq_of_mul_eq_mul_right
      (Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := Q.subgroupOf E))) (hj.trans he.symm)
  have heq : Q ⊓ E = Q := eq_of_le_of_card_ge inf_le_left hcard.le
  exact heq ▸ inf_le_right

/-- Matching image bounds give saturation and both exact image orders. -/
theorem kernel_le_of_card_eq_of_relIndex_bounds (Q J E : Subgroup G) (hQJ : Q ≤ J)
    (hc : Nat.card J = Nat.card E) (m : ℕ)
    (hJ : m ≤ Q.relIndex J) (hE : Q.relIndex E ≤ m) :
    Q ≤ E ∧ Q.relIndex J = m ∧ Q.relIndex E = m := by
  have hi := relIndex_le_of_card_eq_of_le Q J E hQJ hc
  have hj : Q.relIndex J = m := le_antisymm (hi.trans hE) hJ
  have he : Q.relIndex E = m := le_antisymm hE (hJ.trans hi)
  exact ⟨kernel_le_of_card_eq_of_relIndex_eq Q J E hQJ hc (hj.trans he.symm),hj,he⟩
end Subgroup.SmallMover
