module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.WAction.Numerical

/-!
# Exact forward action of the auxiliary word w

Bounded kernel reductions check the literal 80-letter word on every source
label. Balanced-check soundness gives the unconditional intertwining with the
shared `wMap` witness. No cancellation, generator agreement, order, simplicity
or recognition premise is used.

Source: retained ATLAS F24G1-p306936B0 tables and the exact `WordSetup.w` formula.
The candidate and orbit applications are in `WAction.Application`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks

/-- The literal forward w word acts by the shared source-label witness. -/
theorem wWord_apply_labelMap (i : Fin 31671) :
    wordMap letterMap false wLetters (labelMap i) = labelMap (wMap i) := by
  apply WAction.pointTest_sound i
  exact checkPow_sound WAction.pointTest 15 0 WAction.all_checked i.val
    (Nat.zero_le _) (Nat.lt_trans i.isLt (by decide))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks
