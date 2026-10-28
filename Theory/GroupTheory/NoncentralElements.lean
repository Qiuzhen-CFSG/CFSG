module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Transport of noncentral elements

An injective group homomorphism preserves element orders and noncentrality:
a noncommuting pair in the source remains noncommuting in the target.
This is the elementary embedding argument used for the concrete actors in
Aschbacher–Smith, B.5.6, printed p.105.
-/

public section

namespace Theory.GroupTheory
open Subgroup

/-- A noncentral element of prescribed order survives every group embedding. -/
theorem exists_noncentral_orderOf_of_injective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) {n : ℕ}
    (h : ∃ x : G, orderOf x = n ∧ x ∉ center G) :
    ∃ x : H, orderOf x = n ∧ x ∉ center H := by
  obtain ⟨x, hx, hn⟩ := h
  refine ⟨f x, (orderOf_injective f hf x).trans hx, ?_⟩
  intro hc
  apply hn
  rw [mem_center_iff]
  intro y
  apply hf
  simpa only [map_mul] using mem_center_iff.mp hc (f y)

end Theory.GroupTheory
