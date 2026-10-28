module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.SourceActions

/-!
# Staged certificates for the two packed Fi₂₃ candidate actions

The source-label inverse and power tables are exhaustively checked in
`WordChecks.Numerical`. `WordChecks.SourceActions` identifies the resulting
maps with the literal `sourceA` and `sourceB`. The remaining finite contracts
are signed-letter cancellation and the five forward auxiliary-word actions.
They suffice for both requested numerical identities, independently of any
comparison with the cycle-decoded ambient generators.

`WordChecks.Application` applies the reduction to the actual-suborbit consumer,
keeping generator agreement separate from these numerical checks.
Source: GLS3 Table 5.3v, retained ATLAS F24G1-p306936B0 tables, and the exact
candidate formulas in `WordSetup`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient

/-- Reduce the first all-label identity to three forward short-word checks
and numerical signed-letter cancellation. -/
theorem candidateAMap_apply_labelMap_of_auxiliary_checks
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hv : ∀ i, wordMap letterMap false vLetters (labelMap i) = labelMap (WordChecks.vMap i))
    (hr : ∀ i, wordMap letterMap false rLetters (labelMap i) = labelMap (WordChecks.rMap i))
    (hw : ∀ i, wordMap letterMap false wLetters (labelMap i) = labelMap (WordChecks.wMap i)) :
    ∀ i : Fin 31671, candidateAMap (labelMap i) = labelMap (sourceA i) := by
  intro i
  exact (WordChecks.candidateAMap_labelMap_of_short_words
    (WordChecks.inverse_wordMap_labelMap hinv vLetters _ _ WordChecks.vMap_right_inv hv)
    hr
    (WordChecks.inverse_wordMap_labelMap hinv wLetters _ _ WordChecks.wMap_right_inv hw) i).trans
    (congrArg labelMap (WordChecks.smallA_eq_sourceA i))

/-- Reduce the second all-label identity to four forward short-word checks
and the same independent numerical cancellation certificate. -/
theorem candidateBMap_apply_labelMap_of_auxiliary_checks
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hu : ∀ i, wordMap letterMap false uLetters (labelMap i) = labelMap (WordChecks.uMap i))
    (hv : ∀ i, wordMap letterMap false vLetters (labelMap i) = labelMap (WordChecks.vMap i))
    (hw : ∀ i, wordMap letterMap false wLetters (labelMap i) = labelMap (WordChecks.wMap i))
    (hs : ∀ i, wordMap letterMap false sLetters (labelMap i) = labelMap (WordChecks.sMap i)) :
    ∀ i : Fin 31671, candidateBMap (labelMap i) = labelMap (sourceB i) := by
  intro i
  exact (WordChecks.candidateBMap_labelMap_of_short_words hu
    (WordChecks.inverse_wordMap_labelMap hinv uLetters _ _ WordChecks.uMap_right_inv hu)
    hv hw
    (WordChecks.inverse_wordMap_labelMap hinv wLetters _ _ WordChecks.wMap_right_inv hw)
    hs
    (WordChecks.inverse_wordMap_labelMap hinv sLetters _ _ WordChecks.sMap_right_inv hs) i).trans
    (congrArg labelMap (WordChecks.smallB_eq_sourceB i))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient
