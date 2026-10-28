module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordEvaluation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.AuxiliaryData

/-!
# Transport from short-word certificates to the literal candidate evaluators

Forward auxiliary-word comparisons and numerical signed-letter cancellation
supply inverse comparisons. Iteration then transports the exact thirtieth and
sixth powers to maps on the 31671 source labels. No statement about the original
cycle-decoded generators is needed here.

Source: the exact `WordSetup` formulas and `WordEvaluation` definitions.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks

/-- Iterate a source-label map in the same order as `iterateMap`. -/
def iterateSource (f : Fin 31671 → Fin 31671) : Nat → Fin 31671 → Fin 31671
  | 0, i => i
  | k + 1, i => f (iterateSource f k i)

theorem iterateSource_add (f : Fin 31671 → Fin 31671) (k l : Nat) (i : Fin 31671) :
    iterateSource f (k + l) i = iterateSource f k (iterateSource f l i) := by
  induction k with
  | zero => simp only [Nat.zero_add, iterateSource]
  | succ k ih => simp only [Nat.succ_add, iterateSource, ih]

theorem iterateMap_labelMap (f : Fin 306936 → Fin 306936)
    (g : Fin 31671 → Fin 31671) (h : ∀ i, f (labelMap i) = labelMap (g i))
    (k : Nat) (i : Fin 31671) :
    iterateMap f k (labelMap i) = labelMap (iterateSource g k i) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterateMap, ih, h, iterateSource]

/-- A stage boundary for checking a forward word in shorter pieces. -/
theorem wordMap_forward_append (ls ts : List (Fin 4)) (x : Fin 306936) :
    wordMap letterMap false (ls ++ ts) x =
      wordMap letterMap false ls (wordMap letterMap false ts x) := by
  induction ls with
  | nil => rfl
  | cons c cs ih =>
    change letterMap c (wordMap letterMap false (cs ++ ts) x) =
      letterMap c (wordMap letterMap false cs (wordMap letterMap false ts x))
    rw [ih]

/-- Numerical signed-letter cancellation suffices; no source generator is used. -/
theorem inverse_wordMap_forward
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (ls : List (Fin 4)) (x : Fin 306936) :
    wordMap letterMap true ls (wordMap letterMap false ls x) = x := by
  induction ls with
  | nil => rfl
  | cons c cs ih =>
    change wordMap letterMap true cs
      (letterMap (inverseLetter c) (letterMap c (wordMap letterMap false cs x))) = x
    rw [hinv, ih]

/-- Recover an inverse word action from its forward action and a checked
right inverse on source labels. -/
theorem inverse_wordMap_labelMap
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (ls : List (Fin 4)) (f g : Fin 31671 → Fin 31671)
    (hfg : ∀ i, f (g i) = i)
    (hf : ∀ i, wordMap letterMap false ls (labelMap i) = labelMap (f i))
    (i : Fin 31671) :
    wordMap letterMap true ls (labelMap i) = labelMap (g i) := by
  have hi := hf (g i)
  rw [hfg] at hi
  rw [← hi, inverse_wordMap_forward hinv]

/-- The first candidate evaluated wholly on the source labels. -/
def smallA : Fin 31671 → Fin 31671 :=
  iterateSource (fun i => wInvMap (rMap (vInvMap i))) 30

/-- The second candidate evaluated wholly on the source labels. -/
def smallB (i : Fin 31671) : Fin 31671 :=
  uMap (sMap (wMap (iterateSource (fun j => uInvMap (vMap (vMap j))) 6
    (wInvMap (sInvMap (uInvMap i))))))

theorem candidateAMap_labelMap_of_short_words
    (hv : ∀ i, wordMap letterMap true vLetters (labelMap i) = labelMap (vInvMap i))
    (hr : ∀ i, wordMap letterMap false rLetters (labelMap i) = labelMap (rMap i))
    (hw : ∀ i, wordMap letterMap true wLetters (labelMap i) = labelMap (wInvMap i))
    (i : Fin 31671) : candidateAMap (labelMap i) = labelMap (smallA i) := by
  apply iterateMap_labelMap
  intro j
  rw [hv, hr, hw]

theorem candidateBMap_labelMap_of_short_words
    (hu : ∀ i, wordMap letterMap false uLetters (labelMap i) = labelMap (uMap i))
    (hui : ∀ i, wordMap letterMap true uLetters (labelMap i) = labelMap (uInvMap i))
    (hv : ∀ i, wordMap letterMap false vLetters (labelMap i) = labelMap (vMap i))
    (hw : ∀ i, wordMap letterMap false wLetters (labelMap i) = labelMap (wMap i))
    (hwi : ∀ i, wordMap letterMap true wLetters (labelMap i) = labelMap (wInvMap i))
    (hs : ∀ i, wordMap letterMap false sLetters (labelMap i) = labelMap (sMap i))
    (hsi : ∀ i, wordMap letterMap true sLetters (labelMap i) = labelMap (sInvMap i))
    (i : Fin 31671) : candidateBMap (labelMap i) = labelMap (smallB i) := by
  unfold candidateBMap candidateBMapWith
  rw [hui, hsi, hwi]
  have hp (j : Fin 31671) := iterateMap_labelMap
    (fun x => wordMap letterMap true uLetters
      (wordMap letterMap false vLetters (wordMap letterMap false vLetters x)))
    (fun k => uInvMap (vMap (vMap k))) (fun k => by rw [hv, hv, hui]) 6 j
  rw [hp, hw, hs, hu]
  rfl

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks
