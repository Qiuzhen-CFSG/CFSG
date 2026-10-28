/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/NonabelianSimplePerfect.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# NonabelianSimplePerfect

Every nonabelian simple group is perfect.
Simplicity forces the nontrivial commutator subgroup to be the whole group.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/NonabelianSimplePerfect.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.GroupTheory
open scoped IsMulCommutative

theorem nonabelian_simple_perfect (G : Type*) [Group G] [IsSimpleGroup G]
    (hG : ∃ g h : G, g*h ≠ h*g) : Group.IsPerfect G := by
  constructor
  rcases (inferInstance : (commutator G).Normal).eq_bot_or_eq_top with he | he
  · have := (commutator_eq_bot_iff G).mp he
    obtain ⟨g,h,hgh⟩ := hG
    exact (hgh (mul_comm g h)).elim
  · exact he

end Atlas.GroupTheory
