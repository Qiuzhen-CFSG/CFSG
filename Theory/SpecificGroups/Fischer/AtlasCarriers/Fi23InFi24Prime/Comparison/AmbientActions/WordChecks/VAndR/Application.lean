module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.Application

/-!
# Applying the certified v and r actions to the actual candidates

The unconditional certificates remove precisely the v and r premises from the
existing numerical reductions and suborbit application. Signed-letter
cancellation, the other three forward words, and comparison with the original
carrier generators remain separate premises of these consumer adapters.
The parent `WordChecks` assembly owns their discharge.

Source: the exact `WordSetup` candidate formulas, retained ATLAS
F24G1-p306936B0 tables, and the GLS3 Table 5.3v subgroup application.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR

/-- Only the w action and numerical letter cancellation remain for candidate A. -/
theorem candidateAMap_apply_labelMap_of_remaining_checks
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hw : ∀ i, wordMap letterMap false wLetters (labelMap i) = labelMap (wMap i)) :
    ∀ i : Fin 31671, candidateAMap (labelMap i) = labelMap (sourceA i) :=
  candidateAMap_apply_labelMap_of_auxiliary_checks hinv
    vWord_apply_labelMap rWord_apply_labelMap hw

/-- The v premise of the literal candidate B reduction is discharged. -/
theorem candidateBMap_apply_labelMap_of_remaining_checks
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hu : ∀ i, wordMap letterMap false uLetters (labelMap i) = labelMap (uMap i))
    (hw : ∀ i, wordMap letterMap false wLetters (labelMap i) = labelMap (wMap i))
    (hs : ∀ i, wordMap letterMap false sLetters (labelMap i) = labelMap (sMap i)) :
    ∀ i : Fin 31671, candidateBMap (labelMap i) = labelMap (sourceB i) :=
  candidateBMap_apply_labelMap_of_auxiliary_checks hinv hu vWord_apply_labelMap hw hs

/-- The original suborbit consumer with its v and r checks supplied. -/
theorem labelMap_mem_suborbit_of_remaining_checks
    (hgen : ∀ c x, letterMap c x = (letterValue c).val x)
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hu : ∀ i, wordMap letterMap false uLetters (labelMap i) = labelMap (uMap i))
    (hw : ∀ i, wordMap letterMap false wLetters (labelMap i) = labelMap (wMap i))
    (hs : ∀ i, wordMap letterMap false sLetters (labelMap i) = labelMap (sMap i)) :
    ∀ i, labelMap i ∈ suborbit :=
  labelMap_mem_suborbit_of_auxiliary_checks hgen hinv hu
    vWord_apply_labelMap hw rWord_apply_labelMap hs

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR
