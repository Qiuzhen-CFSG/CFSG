module
public import Theory.GroupTheory.SmallMoverFamily

/-!
# Equal-order competitors for a maximum-small-mover join

A subgroup of the same order as a kernel-containing join has at least
as many images modulo that kernel. If its fixed index is small and the
join has enough images, it is admissible. Maximum order then makes it
a member of the family, hence equal to the join.

The neighboring-mover application in MS93 (5.5), printed pp.915--917,
uses this without assuming that the neighboring mover contains the kernel.
-/

public section
open Subgroup
namespace Subgroup.SmallMover
variable {G : Type*} [Group G] [Finite G]

theorem relIndex_le_of_card_eq_of_le (Q J E : Subgroup G) (hQJ : Q ≤ J)
    (hc : Nat.card J = Nat.card E) : Q.relIndex J ≤ Q.relIndex E := by
  have hj := relIndex_mul_relIndex (⊥ : Subgroup G) Q J bot_le hQJ
  rw [relIndex_bot_left,relIndex_bot_left] at hj
  have he := relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ E) E bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right] at he
  have hle : Nat.card (Q ⊓ E : Subgroup G) ≤ Nat.card Q := card_le_of_le inf_le_left
  have hp : 0 < Nat.card Q := Nat.card_pos
  apply Nat.le_of_mul_le_mul_left _ hp
  calc
    Nat.card Q * Q.relIndex J = Nat.card E := hj.trans hc
    _ = Nat.card (Q ⊓ E : Subgroup G) * Q.relIndex E := he.symm
    _ ≤ Nat.card Q * Q.relIndex E := Nat.mul_le_mul_right _ hle

theorem eq_join_of_card_eq_of_index_le (U Q T : Subgroup G) (bound : ℕ) (hbound : 1 ≤ bound)
    (hQJ : Q ≤ join U Q T bound) (hlarge : bound ≤ Q.relIndex (join U Q T bound))
    (E : Subgroup G) (hET : E ≤ T)
    (hc : Nat.card (join U Q T bound) = Nat.card E)
    (hi : (centralizer (E : Set G)).relIndex U ≤ bound) : E = join U Q T bound := by
  have he : Admissible U Q T bound E :=
    ⟨hET,hi.trans (hlarge.trans (relIndex_le_of_card_eq_of_le Q _ E hQJ hc)),hi⟩
  obtain ⟨M,hM⟩ := maximal_nonempty U Q T bound hbound
  have hMJ : M ≤ join U Q T bound := le_sSup hM
  have hEM : E ∈ Maximal U Q T bound :=
    ⟨he,fun D hD => (hM.2 D hD).trans ((card_le_of_le hMJ).trans_eq hc)⟩
  exact eq_of_le_of_card_ge (le_sSup hEM) hc.le
end Subgroup.SmallMover
