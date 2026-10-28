/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Combinatorics/ColoredIncidenceCount.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-!
# Exclusive colored incidences

Partition the incidences by the three membership predicates and count pointwise.

Source: Gerald Höhn, ATLAS, `Atlas/Combinatorics/ColoredIncidenceCount.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies are exposed where the downstream stabilizer constructions use reduction.
-/

@[expose] public section

namespace Atlas.Combinatorics
open scoped BigOperators

/-- Counting exclusive incidences in a bipartition; useful for derived Witt graphs. -/
theorem colored_incidence_count {V : Type*} (S : Finset V) (p q c : V → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred c] :
    (S.filter (fun x => (p x ∧ ¬q x ∧ c x) ∨ (¬p x ∧ q x ∧ ¬c x))).card +
      (S.filter (fun x => p x ∧ q x)).card =
    (S.filter (fun x => p x ∧ c x)).card + (S.filter (fun x => q x ∧ ¬c x)).card := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : p x <;> by_cases hq : q x <;> by_cases hc : c x <;> simp [hp,hq,hc]

end Atlas.Combinatorics
