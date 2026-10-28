module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.WAction.Batch2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.WAction.Batch3

/-!
# Assembly of the complete forward w certificate

Join the four disjoint checked intervals without repeating any word reductions.
Source: `WordEvaluation.wLetters` and the retained ATLAS packed tables.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.WAction

theorem all_checked : checkPow pointTest 0 15 = true :=
  checkPow_join pointTest 14 0
    (checkPow_join pointTest 13 0 batch0_checked batch1_checked)
    (checkPow_join pointTest 13 16384 batch2_checked batch3_checked)

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.WAction
