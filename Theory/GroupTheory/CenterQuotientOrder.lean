module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
/-!
# Center-quotient order under an embedding

The kernel of an embedding followed by the target central quotient lies in
the source center. Indices and Lagrange therefore make the source central
quotient order divide the target central quotient order. This is used in
Aschbacher–Smith 2.4.11 to retain the original subgroup inside its overcomponent.
-/
public section
open Subgroup
namespace Theory.GroupTheory
theorem card_quotient_center_dvd_of_injective {L K : Type*} [Group L] [Group K]
    [Finite L] [Finite K] (f : L →* K) (hf : Function.Injective f) :
    Nat.card (L ⧸ center L) ∣ Nat.card (K ⧸ center K) := by
  let g := (QuotientGroup.mk' (center K)).comp f
  have hk : g.ker ≤ center L := by
    intro x hx
    have hfx : f x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
    apply mem_center_iff.mpr
    intro y
    apply hf
    simpa only [map_mul] using mem_center_iff.mp hfx (f y)
  have hd := index_dvd_of_le hk
  rw [index_ker, index_eq_card] at hd
  exact hd.trans g.range.card_subgroup_dvd_card

end Theory.GroupTheory
