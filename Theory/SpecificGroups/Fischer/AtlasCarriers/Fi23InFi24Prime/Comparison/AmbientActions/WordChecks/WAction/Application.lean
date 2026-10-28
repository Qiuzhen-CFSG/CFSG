module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.WAction
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.Application

/-!
# Applying the checked w action to both Fi₂₃ candidates

The unconditional forward certificate discharges precisely the w premise of
the two literal candidate reductions and their orbit application. Cancellation,
the other auxiliary words and generator agreement remain with their separate
certificate owners and the parent assembly.

Source: the exact `WordSetup` formulas and GLS3 Table 5.3v.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient

/-- The checked w action supplies the w premise of the first candidate. -/
theorem candidateAMap_apply_labelMap_of_auxiliary_checks_except_w
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hv : ∀ i, wordMap letterMap false vLetters (labelMap i) = labelMap (WordChecks.vMap i))
    (hr : ∀ i, wordMap letterMap false rLetters (labelMap i) = labelMap (WordChecks.rMap i)) :
    ∀ i : Fin 31671, candidateAMap (labelMap i) = labelMap (sourceA i) :=
  candidateAMap_apply_labelMap_of_auxiliary_checks hinv hv hr WordChecks.wWord_apply_labelMap

/-- The same forward certificate supplies w in the second candidate, whose
inverse occurrence is recovered by the existing cancellation reduction. -/
theorem candidateBMap_apply_labelMap_of_auxiliary_checks_except_w
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hu : ∀ i, wordMap letterMap false uLetters (labelMap i) = labelMap (WordChecks.uMap i))
    (hv : ∀ i, wordMap letterMap false vLetters (labelMap i) = labelMap (WordChecks.vMap i))
    (hs : ∀ i, wordMap letterMap false sLetters (labelMap i) = labelMap (WordChecks.sMap i)) :
    ∀ i : Fin 31671, candidateBMap (labelMap i) = labelMap (sourceB i) :=
  candidateBMap_apply_labelMap_of_auxiliary_checks hinv hu hv WordChecks.wWord_apply_labelMap hs

/-- The orbit consumer now needs only the other four auxiliary-word checks.
The original-generator comparison remains a separate source obligation. -/
theorem labelMap_mem_suborbit_of_auxiliary_checks_except_w
    (hgen : ∀ c x, letterMap c x = (letterValue c).val x)
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hu : ∀ i, wordMap letterMap false uLetters (labelMap i) = labelMap (WordChecks.uMap i))
    (hv : ∀ i, wordMap letterMap false vLetters (labelMap i) = labelMap (WordChecks.vMap i))
    (hr : ∀ i, wordMap letterMap false rLetters (labelMap i) = labelMap (WordChecks.rMap i))
    (hs : ∀ i, wordMap letterMap false sLetters (labelMap i) = labelMap (WordChecks.sMap i)) :
    ∀ i, labelMap i ∈ suborbit :=
  labelMap_mem_suborbit_of_auxiliary_checks hgen hinv hu hv WordChecks.wWord_apply_labelMap hr hs

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient
