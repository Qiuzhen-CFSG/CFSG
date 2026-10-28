module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.PermutationEvaluation
public import Theory.SpecificGroups.Held.Model.FourPointBase
import Mathlib.Tactic.FinCases

/-!
# Certified generating and middle-factor calculations for Held

The marked subgroup and representatives 1, 9, 4279 generate the actual Held
carrier: checked words recover the two defining ATLAS generators. Twenty-four
checked conjugation equations split the marked subgroup into two left cosets
of its intersection with each moved conjugate. Word induction proves the
splitting for every subgroup element. Neither group order nor simplicity is
used. The GAP word candidates are retained in `source` beside `Data.lean`.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets
open Theory.GroupTheory.DoubleCosetTransitions

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
private theorem recover_a : eval generator recoveryA = a := by
  apply Held.eq_of_four_point_images
  simp only [representation_eval, representation_generator]
  decide +kernel


set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem recover_b : eval generator recoveryB = b := by
  apply Held.eq_of_four_point_images
  simp only [representation_eval, representation_generator]
  decide +kernel


/-- These seven concrete elements generate the existing ATLAS carrier. -/
public theorem generation :
    Subgroup.closure ((markedSubgroup : Set He) ∪ Set.range move) = ⊤ := by
  let K := Subgroup.closure ((markedSubgroup : Set He) ∪ Set.range move)
  have hgen (i : Fin 7) : generator i ∈ K := by
    refine Fin.addCases (n := 3) (m := 4) (fun j => ?_) (fun j => ?_) i
    · simp only [generator, Fin.addCases_left]
      exact Subgroup.subset_closure (Or.inl (markedGenerator_mem j))
    · simp only [generator, Fin.addCases_right]
      exact Subgroup.subset_closure (Or.inr ⟨j, rfl⟩)
  have ha : a ∈ K := recover_a ▸ eval_mem generator K hgen recoveryA
  have hb : b ∈ K := recover_b ▸ eval_mem generator K hgen recoveryB
  apply top_unique
  rw [← Held.closure_pair]
  apply (Subgroup.closure_le K).mpr
  intro x hx
  rcases hx with rfl | hx
  · exact ha
  · obtain rfl := Set.mem_singleton_iff.mp hx
    exact hb


end Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets
