module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.CandidateTables.WordChecks.Assembly
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.CandidateTables.WordChecks.Checker

/-!
# Full-domain word-certificate assembly for the Fi₂₃ candidates

The shared dictionary reduces the five long words to eleven two-map checks
and five shorter output checks. `WordChecks.Assembly` proves their exact
interpretations on every ambient point. The applications below supply all
five word comparisons to the unchanged candidate assembly and retain the
independent numerical and signed-letter cancellation premises explicitly.

The three word-check records are still finite certificate obligations.
They are not assumptions of the source theorem and must be discharged before
claiming unconditional word comparisons. Final source identification belongs
to the parent full-candidate assembly.

Source: the literal `WordSetup` and `WordEvaluation` words, retained ATLAS
F24G1-p306936B0, and GLS3 Table 5.3v. See `WordChecks/source/README.md`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables
open Certificate Certificate.Ambient

/-- Apply the three A-family word interpretations to the literal thirtieth power. -/
theorem candidateAMap_eq_imageA_of_wordChecks
    (hd : WordChecks.DictionaryChecks) (ho : WordChecks.OutputChecksA)
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hi : InverseChecks) (ha : PowerChecksA) (x : Fin 306936) :
    candidateAMap x = FirstFourModel.imageA x :=
  candidateAMap_eq_imageA_of_stages hinv hi ha
    (WordChecks.vMap_correct_of_checks hd ho)
    (WordChecks.rMap_correct_of_checks hd ho)
    (WordChecks.wMap_correct_of_checks hd ho) x

/-- Supply all four words in the literal sixth power and its two conjugating sides. -/
theorem candidateBMap_eq_imageB_of_wordChecks
    (hd : WordChecks.DictionaryChecks)
    (hoa : WordChecks.OutputChecksA) (hob : WordChecks.OutputChecksB)
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hi : InverseChecks) (hb : PowerChecksB) (x : Fin 306936) :
    candidateBMap x = FirstFourModel.imageB x :=
  candidateBMap_eq_imageB_of_stages hinv hi hb
    (WordChecks.uMap_correct_of_checks hd hob)
    (WordChecks.vMap_correct_of_checks hd hoa)
    (WordChecks.wMap_correct_of_checks hd hoa)
    (WordChecks.sMap_correct_of_checks hd hob) x

end Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables
