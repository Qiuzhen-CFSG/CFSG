module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.CandidateTables.NumericalChecks.Certificate

/-!
# Certified full-ambient inverse and composition stages

Bounded kernel checks establish the four auxiliary inverse laws, the seven
steps of the thirtieth-power chain, and the five steps of the sixth-power chain
and its final conjugation. These supply the three numerical records used by
`Reduction` without any additional hypothesis.

The two applications below discharge precisely those stage premises in the
literal candidate-table comparisons. Forward-word comparisons and cancellation
of signed letters remain explicit; their discharge and final permutation
assembly belong to the full candidate-table comparison owner.

Source: the exact `WordSetup` formulas, retained ATLAS F24G1-p306936B0 data,
and GLS3 Table 5.3v. Witness reproduction and attribution remain unchanged in
`CandidateTables/source/` and `AtlasCarriers/source/`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables
open Certificate.Ambient

/-- All four auxiliary right inverses, on the entire ambient set. -/
theorem inverseChecks : InverseChecks :=
  inverseChecks_of_test fun i =>
    (NumericalChecks.stageTest_sound i.val (NumericalChecks.stages_checked i)).1

/-- The complete short addition chain for the first candidate. -/
theorem powerChecksA : PowerChecksA :=
  powerChecksA_of_test fun i =>
    (NumericalChecks.stageTest_sound i.val (NumericalChecks.stages_checked i)).2.1

/-- The second addition chain, including both sides of its conjugation. -/
theorem powerChecksB : PowerChecksB :=
  powerChecksB_of_test fun i =>
    (NumericalChecks.stageTest_sound i.val (NumericalChecks.stages_checked i)).2.2

/-- The numerical A stages are discharged; only the independent word and
signed-letter premises remain for the full candidate-table assembly. -/
theorem candidateAMap_eq_imageA_of_words
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hv : ∀ x, wordMap letterMap false vLetters x = vMap x)
    (hr : ∀ x, wordMap letterMap false rLetters x = rMap x)
    (hw : ∀ x, wordMap letterMap false wLetters x = wMap x)
    (x : Fin 306936) : candidateAMap x = FirstFourModel.imageA x :=
  candidateAMap_eq_imageA_of_stages hinv inverseChecks powerChecksA hv hr hw x

/-- The numerical B stages are discharged, preserving the literal final
conjugation and all remaining word and signed-letter premises. -/
theorem candidateBMap_eq_imageB_of_words
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hu : ∀ x, wordMap letterMap false uLetters x = uMap x)
    (hv : ∀ x, wordMap letterMap false vLetters x = vMap x)
    (hw : ∀ x, wordMap letterMap false wLetters x = wMap x)
    (hs : ∀ x, wordMap letterMap false sLetters x = sMap x)
    (x : Fin 306936) : candidateBMap x = FirstFourModel.imageB x :=
  candidateBMap_eq_imageB_of_stages hinv inverseChecks powerChecksB hu hv hw hs x

end Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables
