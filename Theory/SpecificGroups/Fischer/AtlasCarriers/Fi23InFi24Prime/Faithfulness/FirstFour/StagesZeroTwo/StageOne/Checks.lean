module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.TableChecks

/-!
# Algebra of the stage-one tree

All tree Schreier permutations are identity by cancellation of their literal
words. Incoming point images then identify the images of all inverse word
representatives. The checked root fiber supplies base-return separation.
Finally a right-coset edge at `prev a j` gives the required positive left
transition at `j`, with the same actual subgroup factor.

Source: elementary Schreier rewriting for the ATLAS F24G1-p306936B0 words;
GLS3 Table 5.3v. The point images and nontree memberships remain explicit.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne

theorem prev_next (a : Fin 2) (j : Vertex) : prev a (next a j) = j :=
  ((table_facts j).1 a).1

theorem next_prev (a : Fin 2) (j : Vertex) : next a (prev a j) = j :=
  ((table_facts j).1 a).2

theorem root_fiber (j : Vertex) (h : label j = label root) : j = root :=
  (table_facts j).2.1 h

theorem incoming_isTree (j : Vertex) (hj : j ≠ root) :
    IsTree (letter j) (parent j) := by
  have h := (table_facts j).2.2 hj
  exact ⟨by simpa only [h] using hj, by rw [h], by rw [h]⟩

/-- Full permutation equality, obtained without evaluating any ambient label. -/
theorem tree_schreier_eq_one (a : Fin 2) (j : Vertex) (h : IsTree a j) :
    schreier a j = 1 := by
  have hr := rightRep_parent (next a j) h.1
  rw [h.2.1, h.2.2] at hr
  simp only [schreier, hr, mul_inv_cancel]

theorem incoming_schreier_eq_one (j : Vertex) (hj : j ≠ root) :
    schreier (letter j) (parent j) = 1 :=
  tree_schreier_eq_one _ _ (incoming_isTree j hj)

theorem all_edges_of_nonTree (he : NonTreeEdges) (a : Fin 2) (j : Vertex) :
    schreier a j ∈ stage 2 := by
  by_cases h : IsTree a j
  · rw [tree_schreier_eq_one a j h]
    exact (stage 2).one_mem
  · exact he a j h

/-- Tree point checks suffice; no orbit-cardinality or faithfulness hypothesis is used. -/
theorem representative_apply_root (ha : TreeAction) (j : Vertex) :
    representative j (label root) = label j := by
  refine (measure (fun k : Vertex => k.val)).wf.induction
    (C := fun k => representative k (label root) = label k) j ?_
  intro j ih
  by_cases hj : j = root
  · subst j
    rw [root_representative]
    rfl
  rw [representative, rightRep_parent j hj, mul_inv_rev, Equiv.Perm.mul_apply]
  change (gen (letter j))⁻¹ (representative (parent j) (label root)) = label j
  rw [ih (parent j) (parent_lt j hj)]
  exact (gen (letter j)).symm_apply_eq.mpr (ha j hj).symm

theorem returns_base (ha : TreeAction) (j : Vertex)
    (h : representative j (point 1) = point 1) : representative j = 1 := by
  rw [point_eq_root_label, representative_apply_root ha] at h
  rw [root_fiber j h, root_representative]

/-- Right-coset data give a positive LEFT step, with no change of ambient action. -/
theorem positive_step (a : Fin 2) (j : Vertex) :
    generators 1 a * representative j =
      representative (prev a j) * schreier a (prev a j) := by
  simp only [representative, schreier, next_prev, mul_assoc, inv_mul_cancel_left, gen]

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne
