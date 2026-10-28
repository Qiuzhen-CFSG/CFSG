module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Check

/-!
# Assembly of the final-four ambient transition certificates

The generic word transport and the sound numerical evaluator reduce the
literal `StepIdentities` to two independent obligations: identifying the ten
stage-generator tables with the model words, and checking the 167 nonformal
transitions on all ambient letters. The other 77 transitions follow directly
from their words. The candidate comparisons remain with the enclosing
last-four stabilizer-reduction assembly.

This is presently conditional on both finite obligations. It does not yet
assert `stepIdentities_of_compared_candidates`. The result below supplies
exactly the premise consumed by `LastFour.reduction` and
`wordStage_last_four_reductions_of_certificates`, with their literal quotient-
free carrier and left-action multiplication conventions.

Source: ATLAS F24G1-p306936B0 and GLS3 Table 5.3v; see
`LastFour/source/README.md` and `Transitions/source/README.md`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour

/-- Complete transport from independently certified tables and short words.
The two finite premises must be discharged before asserting the target helper. -/
theorem stepIdentities_of_compared_candidates_of_checks
    (ha : candidateA.val = FirstFourModel.aPerm)
    (hb : candidateB.val = FirstFourModel.bPerm)
    (tables : Transitions.TableAgreement) (checks : Transitions.EssentialChecks) :
    StepIdentities := by
  intro i a j
  cases h : Transitions.formalEntry i a j with
  | false => exact Transitions.step_of_table_checks ha hb tables i a j (checks i a j h)
  | true => exact Transitions.step_of_formalEntry i a j h

end Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour
