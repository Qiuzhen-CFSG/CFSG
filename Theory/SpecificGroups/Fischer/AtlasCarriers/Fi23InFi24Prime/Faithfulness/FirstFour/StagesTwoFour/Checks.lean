module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.TableChecks

/-!
# Consequences of the checked right-coset trees

The inverse columns, isolated base label, and incoming tree words yield the
structural lemmas used by the two-stage reduction. Keeping these proofs apart
from the numerical checks avoids repeating their reductions during proof repair.
Source: ATLAS F24G1-p306936B0, retained `source/trees.json`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour

theorem prev_next (i a : Fin 2) (j : Fin (size i)) : prev i a (next i a j) = j :=
  ((table_facts i j).1 a).1

theorem next_prev (i a : Fin 2) (j : Fin (size i)) : next i a (prev i a j) = j :=
  ((table_facts i j).1 a).2

theorem root_fiber (i : Fin 2) (j : Fin (size i))
    (h : label i j = label i (root i)) : j = root i :=
  (table_facts i j).2.1 h

/-- All tree Schreier factors are the identity in the actual permutation group. -/
theorem tree_schreier_eq_one (i a : Fin 2) (j : Fin (size i)) (h : IsTree i a j) :
    schreier i a j = 1 := by
  have hw := ((table_facts i (next i a j)).2.2 h.1).1
  rw [h.2.1, h.2.2] at hw
  have hr : representative i (next i a j) = representative i j * gen i a := by
    simp only [representative, hw, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  simp only [schreier, hr, mul_inv_cancel]

/-- Every listed nonroot vertex has its specified incoming tree edge. -/
theorem incoming_isTree (i : Fin 2) (j : Fin (size i)) (h : j ≠ root i) :
    IsTree i (letter i j) (parent i j) := by
  have hs := ((table_facts i j).2.2 h).2.1
  exact ⟨by simpa only [hs] using h, by rw [hs], by rw [hs]⟩

theorem incoming_schreier_eq_one (i : Fin 2) (j : Fin (size i)) (h : j ≠ root i) :
    schreier i (letter i j) (parent i j) = 1 :=
  tree_schreier_eq_one i (letter i j) (parent i j) (incoming_isTree i j h)

/-- Add the checked tree edges to the genuinely missing nontree memberships. -/
theorem all_edges_of_nonTree (h : NonTreeEdges) (i a : Fin 2) (j : Fin (size i)) :
    schreier i a j ∈ stage (i.natAdd 2).succ := by
  by_cases ht : IsTree i a j
  · rw [tree_schreier_eq_one i a j ht]
    exact (stage _).one_mem
  · exact h i a j ht

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour
