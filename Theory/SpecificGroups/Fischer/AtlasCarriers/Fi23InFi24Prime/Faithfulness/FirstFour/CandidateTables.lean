module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.PackedData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordEvaluation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.CandidateTables.Reduction
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.Model

/-!
# Full ambient candidate-table interface

The two numerical tables in `FirstFour.PackedData` are the proposed values of
the literal candidate words on every ambient letter.  The exhaustive
certificate comparing those tables with the packed word evaluators belongs in
the extension modules below this file; it is intentionally kept separate from
the word interpretation and from the finite stabilizer model.

This module records the exact assembly boundary.  The hypotheses of the two
assembly lemmas are pointwise equalities on the *entire* ambient set, so a
later certificate cannot accidentally prove only the image of a relabeling.
The signed-letter consumers below also take the staged certificates from
`Reduction`, which converts five forward word comparisons and short numerical
checks into the required full-domain identities. Those checks remain explicit
until their exhaustive certificates are constructed.

Source: GLS3 Table 5.3v and the Fi₂₄′ ATLAS representation
F24G1-p306936B0; numerical data and attribution are retained in
`AtlasCarriers/source/` and reproduced by
`Faithfulness/FirstFour/source/generate_model.py`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift

open Certificate

namespace CandidateTables

/- The hypotheses below are intentionally pointwise over all 306936 letters.
   They are the contract discharged by the exhaustive staged certificate. -/

theorem candidateA_eq_model_of_check
    (h : ∀ x : Fin 306936,
      Certificate.Ambient.candidateAMap x = FirstFourModel.imageA x) :
    Certificate.Ambient.candidateAMap = FirstFourModel.imageA := by
  funext x
  exact h x

theorem candidateB_eq_model_of_check
    (h : ∀ x : Fin 306936,
      Certificate.Ambient.candidateBMap x = FirstFourModel.imageB x) :
    Certificate.Ambient.candidateBMap = FirstFourModel.imageB := by
  funext x
  exact h x

theorem candidateA_val_eq_model_of_check
    (hf : ∀ c x, Certificate.Ambient.letterMap c x =
      (Certificate.Ambient.letterValue c).val x)
    (h : ∀ x : Fin 306936,
      Certificate.Ambient.candidateAMap x = FirstFourModel.imageA x) :
    candidateA.val = FirstFourModel.imageA := by
  funext x
  exact (Certificate.Ambient.candidateAMap_correct
    hf x).symm.trans (h x)

theorem candidateB_val_eq_model_of_check
    (hf : ∀ c x, Certificate.Ambient.letterMap c x =
      (Certificate.Ambient.letterValue c).val x)
    (h : ∀ x : Fin 306936,
      Certificate.Ambient.candidateBMap x = FirstFourModel.imageB x) :
    candidateB.val = FirstFourModel.imageB := by
  funext x
  exact (Certificate.Ambient.candidateBMap_correct
    hf x).symm.trans (h x)

/-- The first full-domain comparison identifies the actual model permutation. -/
theorem candidateA_val_eq_model_perm_of_check
    (hf : ∀ c x, Certificate.Ambient.letterMap c x =
      (Certificate.Ambient.letterValue c).val x)
    (h : ∀ x : Fin 306936,
      Certificate.Ambient.candidateAMap x = FirstFourModel.imageA x) :
    candidateA.val = FirstFourModel.aPerm := by
  apply Equiv.ext
  intro x
  exact (Certificate.Ambient.candidateAMap_correct hf x).symm.trans (h x)

/-- The second comparison preserves the literal sixth power and conjugation. -/
theorem candidateB_val_eq_model_perm_of_check
    (hf : ∀ c x, Certificate.Ambient.letterMap c x =
      (Certificate.Ambient.letterValue c).val x)
    (h : ∀ x : Fin 306936,
      Certificate.Ambient.candidateBMap x = FirstFourModel.imageB x) :
    candidateB.val = FirstFourModel.bPerm := by
  apply Equiv.ext
  intro x
  exact (Certificate.Ambient.candidateBMap_correct hf x).symm.trans (h x)

/-- Actual FirstFour consumer of the staged A certificate. The assembly owner
must supply the three forward words, the inverse laws, and the short A checks. -/
theorem candidateA_val_eq_model_perm_of_stages
    (hf : ∀ c x, Ambient.letterMap c x = (Ambient.letterValue c).val x)
    (hinv : ∀ c x, Ambient.letterMap (Ambient.inverseLetter c) (Ambient.letterMap c x) = x)
    (hi : InverseChecks) (ha : PowerChecksA)
    (hv : ∀ x, Ambient.wordMap Ambient.letterMap false Ambient.vLetters x = vMap x)
    (hr : ∀ x, Ambient.wordMap Ambient.letterMap false Ambient.rLetters x = rMap x)
    (hw : ∀ x, Ambient.wordMap Ambient.letterMap false Ambient.wLetters x = wMap x) :
    candidateA.val = FirstFourModel.aPerm :=
  candidateA_val_eq_model_perm_of_check hf
    (candidateAMap_eq_imageA_of_stages hinv hi ha hv hr hw)

/-- Actual FirstFour consumer of the staged B certificate, with every extra
numerical and word premise visible for final discharge. -/
theorem candidateB_val_eq_model_perm_of_stages
    (hf : ∀ c x, Ambient.letterMap c x = (Ambient.letterValue c).val x)
    (hinv : ∀ c x, Ambient.letterMap (Ambient.inverseLetter c) (Ambient.letterMap c x) = x)
    (hi : InverseChecks) (hb : PowerChecksB)
    (hu : ∀ x, Ambient.wordMap Ambient.letterMap false Ambient.uLetters x = uMap x)
    (hv : ∀ x, Ambient.wordMap Ambient.letterMap false Ambient.vLetters x = vMap x)
    (hw : ∀ x, Ambient.wordMap Ambient.letterMap false Ambient.wLetters x = wMap x)
    (hs : ∀ x, Ambient.wordMap Ambient.letterMap false Ambient.sLetters x = sMap x) :
    candidateB.val = FirstFourModel.bPerm :=
  candidateB_val_eq_model_perm_of_check hf
    (candidateBMap_eq_imageB_of_stages hinv hi hb hu hv hw hs)

end CandidateTables

end Sporadic.Fischer.Fi24Prime.Fi23Lift
