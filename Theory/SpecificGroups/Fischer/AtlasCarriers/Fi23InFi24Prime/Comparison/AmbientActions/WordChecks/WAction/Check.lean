module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordEvaluation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.AuxiliaryData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Check

/-!
# The finite predicate for the forward w action

The check uses the literal 80-letter evaluator, packed signed generators and
source-label witness. Indices beyond the 31671 labels are ignored, allowing a
balanced check on 32768 indices without repeating any labels.

Source: the retained ATLAS F24G1-p306936B0 tables, `WordSetup.w`, and the
witness in `WordChecks.AuxiliaryData`. No generator comparison is assumed.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.WAction

def pointTest (n : Nat) : Bool :=
  let i := Fin.ofNat 31671 n
  if n < 31671 then
    decide (wordMap letterMap false wLetters (labelMap i) = labelMap (wMap i))
  else true

theorem pointTest_sound (i : Fin 31671) (h : pointTest i.val = true) :
    wordMap letterMap false wLetters (labelMap i) = labelMap (wMap i) := by
  have hi : Fin.ofNat 31671 i.val = i := by simp
  simpa only [pointTest, if_pos i.isLt, hi, decide_eq_true_eq] using h

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.WAction
