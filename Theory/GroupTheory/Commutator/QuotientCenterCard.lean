module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# Cardinality of a subgroup central modulo a normal subgroup

If N ≤ H and [H,Q] ≤ N, the image of H in Q/N lies in the center.
The order formula for that image gives |H| ≤ |N| |Z(Q/N)|.

The original weight-four residual in Aschbacher–Smith 13.4.15, printed
p.912, applies this to its sixteen-group and the literal involution line.
-/

public section
open scoped commutatorElement
namespace Subgroup

/-- The image of H in Q/N is central, so its order bounds |H|/|N|. -/
theorem card_le_card_center_quotient_mul {Q : Type*} [Group Q] [Finite Q]
    (H N : Subgroup Q) [N.Normal] (hNH : N ≤ H) (hc : ⁅H,⊤⁆ ≤ N) :
    Nat.card H ≤ Nat.card N * Nat.card (center (Q ⧸ N)) := by
  let q := QuotientGroup.mk' N
  have hm : H.map q ≤ center (Q ⧸ N) := by
    rintro x ⟨a,ha,rfl⟩
    apply mem_center_iff.mpr
    intro b
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective N b
    have hh : q ⁅a,b⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr
      (hc (commutator_mem_commutator ha (mem_top b)))
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hh
    exact hh.symm
  have hi : N.relIndex H = Nat.card (H.map q) := by
    simpa only [q,QuotientGroup.ker_mk'] using (relIndex_ker H q)
  have hs := relIndex_mul_relIndex (⊥ : Subgroup Q) N H bot_le hNH
  rw [relIndex_bot_left,relIndex_bot_left,hi] at hs
  rw [←hs]
  exact Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective
    (inclusion hm) (inclusion_injective _))

end Subgroup
