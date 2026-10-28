/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/CenterSimpleQuotient.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Centers of groups with simple central quotients

A nonabelian simple quotient has trivial center, so a central subgroup defining that quotient is the full center.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/CenterSimpleQuotient.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

namespace Atlas.GroupTheory

/-- A nonabelian simple group has trivial center. -/
theorem center_eq_bot_of_simple_nonabelian (G : Type*) [Group G] [IsSimpleGroup G]
    (hn : ¬IsMulCommutative G) : Subgroup.center G=⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h|h
  · exact h
  · exact (hn (Subgroup.center_eq_top_iff.mp h)).elim

/-- If a central quotient is nonabelian simple, the divided-out subgroup was
already the entire center. No finiteness hypothesis is needed. -/
theorem center_eq_of_simple_quotient (G : Type*) [Group G]
    (Z : Subgroup G) [Z.Normal] (hz : Z ≤ Subgroup.center G)
    [IsSimpleGroup (G ⧸ Z)] (hn : ¬IsMulCommutative (G ⧸ Z)) :
    Subgroup.center G=Z := by
  apply le_antisymm ?_ hz
  intro x hx
  have hm : QuotientGroup.mk' Z x ∈ Subgroup.center (G ⧸ Z) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z q
    simpa only [map_mul] using congrArg (QuotientGroup.mk' Z) (hx y)
  rw [center_eq_bot_of_simple_nonabelian (G ⧸ Z) hn,Subgroup.mem_bot] at hm
  exact (QuotientGroup.eq_one_iff x).mp hm

end Atlas.GroupTheory
