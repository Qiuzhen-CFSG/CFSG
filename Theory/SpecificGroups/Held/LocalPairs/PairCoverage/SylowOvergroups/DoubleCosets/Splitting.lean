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
set_option maxHeartbeats 16000000 in
private theorem split_equations (i : Fin 3) (j : Fin 4) (e : Bool) :
    (move i)⁻¹ * (middle i (splitNext i j e))⁻¹ * markedGenerator j *
      middle i e * move i = eval markedGenerator (splitWord i j e) := by
  apply Held.eq_of_four_point_images
  simp only [map_mul, map_inv, representation_move, representation_middle,
    representation_markedGenerator, representation_eval]
  fin_cases i <;> fin_cases j <;> cases e <;> decide +kernel


/-- Every element has a middle factor from the published two-element list.
The remaining factor conjugates into the marked subgroup in the needed direction. -/
public theorem middle_split (i : Fin 3) (s : He) (hs : s ∈ markedSubgroup) :
    ∃ e c, c ∈ markedSubgroup ∧ (move i)⁻¹ * c * move i ∈ markedSubgroup ∧
      s = middle i e * c := by
  apply conjugate_split_of_steps markedSubgroup markedGenerator rfl (move i)
    (middle i) ⟨false, rfl⟩ ?_ hs
  intro j e
  let c := (middle i (splitNext i j e))⁻¹ * markedGenerator j * middle i e
  refine ⟨splitNext i j e, c, ?_, ?_, ?_⟩
  · exact markedSubgroup.mul_mem
      (markedSubgroup.mul_mem (markedSubgroup.inv_mem (middle_mem _ _))
        (markedGenerator_mem _)) (middle_mem _ _)
  · change (move i)⁻¹ * ((middle i (splitNext i j e))⁻¹ * markedGenerator j *
      middle i e) * move i ∈ markedSubgroup
    rw [← mul_assoc, ← mul_assoc, split_equations]
    exact eval_mem markedGenerator markedSubgroup markedGenerator_mem _
  · simp only [c, mul_assoc, mul_inv_cancel_left]

end Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets
