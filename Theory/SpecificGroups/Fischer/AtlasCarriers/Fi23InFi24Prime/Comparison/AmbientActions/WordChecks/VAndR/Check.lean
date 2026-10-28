module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.AuxiliaryData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordEvaluation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Check

/-!
# Boolean specification of the two forward word actions

The check evaluates the literal 79-letter v word and 77-letter r word on the
shared label map. The source-label witnesses are the existing `vMap` and `rMap`;
no generator comparison or signed-letter cancellation is used.

Source: retained ATLAS F24G1-p306936B0 tables, the exact `WordSetup` lists,
and `WordChecks/source/README.md`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR

/-- Both literal forward-word comparisons at one source label. -/
def pointTest (n : Nat) : Bool :=
  let i := Fin.ofNat 31671 n
  decide (wordMap letterMap false vLetters (labelMap i) = labelMap (vMap i) ∧
    wordMap letterMap false rLetters (labelMap i) = labelMap (rMap i))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR
