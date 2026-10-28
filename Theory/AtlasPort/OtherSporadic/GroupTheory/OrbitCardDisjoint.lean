/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/OrbitCardDisjoint.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Disjoint orbit families

Distinct orbit cardinalities imply disjointness; only equal-cardinality families require separate invariants.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/OrbitCardDisjoint.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

namespace Atlas.GroupTheory

/-- Full orbits of different cardinalities are disjoint. No finiteness
assumption is needed beyond the displayed inequality of natural cardinalities. -/
theorem orbit_families_disjoint_of_card_ne {H X : Type*} [Group H] [MulAction H X]
    (S T : Set X) (x y : X) (hS : S=MulAction.orbit H x) (hT : T=MulAction.orbit H y)
    (hcard : Nat.card S≠Nat.card T) : Disjoint S T := by
  rw [hS,hT] at hcard ⊢
  exact (MulAction.orbit.eq_or_disjoint x y).resolve_left
    (fun h => hcard (congrArg (fun U : Set X => Nat.card U) h))

/-- Once full orbit identification is established, only repeated cardinalities
require a separate invariant to prove an indexed family pairwise disjoint. -/
theorem orbit_families_pairwise_disjoint {H X I : Type*} [Group H] [MulAction H X]
    (F : I → Set X) (horbit : ∀ i, ∃ x : X, F i=MulAction.orbit H x)
    (hrepeated : ∀ i j, i≠j → Nat.card (F i)=Nat.card (F j) → Disjoint (F i) (F j)) :
    Pairwise (fun i j => Disjoint (F i) (F j)) := by
  intro i j hij
  by_cases hc : Nat.card (F i)=Nat.card (F j)
  · exact hrepeated i j hij hc
  · obtain ⟨x,hx⟩ := horbit i
    obtain ⟨y,hy⟩ := horbit j
    exact orbit_families_disjoint_of_card_ne (F i) (F j) x y hx hy hc

theorem orbit_families_pairwise_disjoint_of_degrees {H X I : Type*} [Group H] [MulAction H X]
    (F : I → Set X) (d : I → ℕ) (hcard : ∀ i, Nat.card (F i)=d i)
    (horbit : ∀ i, ∃ x : X, F i=MulAction.orbit H x)
    (hrepeated : ∀ i j, i≠j → d i=d j → Disjoint (F i) (F j)) :
    Pairwise (fun i j => Disjoint (F i) (F j)) := by
  apply orbit_families_pairwise_disjoint F horbit
  intro i j hij hc
  rw [hcard i,hcard j] at hc
  exact hrepeated i j hij hc

end Atlas.GroupTheory
