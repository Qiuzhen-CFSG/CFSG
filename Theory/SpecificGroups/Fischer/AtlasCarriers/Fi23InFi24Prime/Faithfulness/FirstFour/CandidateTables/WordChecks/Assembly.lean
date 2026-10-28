module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.CandidateTables.WordChecks.Contracts

/-!
# Sound assembly of all five ambient word comparisons

Each dictionary interpretation follows from a two-map check and exact forward
composition. Flattening the dictionary words reproduces the literal source
lists after the definitionally valid replacement of signed letter 2 by 0.
The output checks then give the entire ambient comparisons, with no restriction
to the image of labelMap. The numerical contracts remain explicit until the
independent exhaustive certificates have been built.

Source: `WordSetup`, `WordEvaluation`, retained ATLAS F24G1-p306936B0,
and GLS3 Table 5.3v.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables.WordChecks
open Certificate Certificate.Ambient

private def normalizeLetter (c : Fin 4) : Fin 4 :=
  if c = 2 then 0 else c

private theorem letterMap_normalize (c : Fin 4) :
    letterMap (normalizeLetter c) = letterMap c := by
  fin_cases c <;> rfl

private theorem wordMap_normalize (ls : List (Fin 4)) (x : Fin 306936) :
    wordMap letterMap false (ls.map normalizeLetter) x =
      wordMap letterMap false ls x := by
  induction ls with
  | nil => rfl
  | cons c cs ih =>
    change letterMap (normalizeLetter c)
      (wordMap letterMap false (cs.map normalizeLetter) x) =
        letterMap c (wordMap letterMap false cs x)
    rw [letterMap_normalize, ih]

theorem wordMap_flatten (pieces : List (List (Fin 4))) (x : Fin 306936) :
    wordMap letterMap false pieces.flatten x =
      pieces.foldr (fun ls y => wordMap letterMap false ls y) x := by
  induction pieces with
  | nil => rfl
  | cons ls pieces ih =>
    change wordMap letterMap false (ls ++ pieces.flatten) x = _
    rw [wordMap_append, ih]
    rfl

theorem d04Map_correct (h : DictionaryChecks) (x : Fin 306936) :
    wordMap letterMap false d04Letters x = d04Map x := by
  change wordMap letterMap false ([0] ++ [3]) x = _
  rw [wordMap_append]
  exact (h.d04 x).symm

theorem d05Map_correct (h : DictionaryChecks) (x : Fin 306936) :
    wordMap letterMap false d05Letters x = d05Map x := by
  change wordMap letterMap false ([0] ++ [1]) x = _
  rw [wordMap_append]
  exact (h.d05 x).symm

theorem d06Map_correct (h : DictionaryChecks) (x : Fin 306936) :
    wordMap letterMap false d06Letters x = d06Map x := by
  change wordMap letterMap false (d04Letters ++ d04Letters) x = _
  rw [wordMap_append]
  rw [d04Map_correct h]
  rw [d04Map_correct h]
  exact (h.d06 x).symm

theorem d07Map_correct (h : DictionaryChecks) (x : Fin 306936) :
    wordMap letterMap false d07Letters x = d07Map x := by
  change wordMap letterMap false (d05Letters ++ d05Letters) x = _
  rw [wordMap_append]
  rw [d05Map_correct h]
  rw [d05Map_correct h]
  exact (h.d07 x).symm

theorem d08Map_correct (h : DictionaryChecks) (x : Fin 306936) :
    wordMap letterMap false d08Letters x = d08Map x := by
  change wordMap letterMap false (d04Letters ++ d05Letters) x = _
  rw [wordMap_append]
  rw [d04Map_correct h]
  rw [d05Map_correct h]
  exact (h.d08 x).symm

theorem d09Map_correct (h : DictionaryChecks) (x : Fin 306936) :
    wordMap letterMap false d09Letters x = d09Map x := by
  change wordMap letterMap false (d04Letters ++ d07Letters) x = _
  rw [wordMap_append]
  rw [d04Map_correct h]
  rw [d07Map_correct h]
  exact (h.d09 x).symm

theorem d10Map_correct (h : DictionaryChecks) (x : Fin 306936) :
    wordMap letterMap false d10Letters x = d10Map x := by
  change wordMap letterMap false (d08Letters ++ d06Letters) x = _
  rw [wordMap_append]
  rw [d08Map_correct h]
  rw [d06Map_correct h]
  exact (h.d10 x).symm

theorem d11Map_correct (h : DictionaryChecks) (x : Fin 306936) :
    wordMap letterMap false d11Letters x = d11Map x := by
  change wordMap letterMap false (d07Letters ++ d06Letters) x = _
  rw [wordMap_append]
  rw [d07Map_correct h]
  rw [d06Map_correct h]
  exact (h.d11 x).symm

theorem d12Map_correct (h : DictionaryChecks) (x : Fin 306936) :
    wordMap letterMap false d12Letters x = d12Map x := by
  change wordMap letterMap false (d05Letters ++ d06Letters) x = _
  rw [wordMap_append]
  rw [d05Map_correct h]
  rw [d06Map_correct h]
  exact (h.d12 x).symm

theorem d13Map_correct (h : DictionaryChecks) (x : Fin 306936) :
    wordMap letterMap false d13Letters x = d13Map x := by
  change wordMap letterMap false (d10Letters ++ d07Letters) x = _
  rw [wordMap_append]
  rw [d10Map_correct h]
  rw [d07Map_correct h]
  exact (h.d13 x).symm

theorem d14Map_correct (h : DictionaryChecks) (x : Fin 306936) :
    wordMap letterMap false d14Letters x = d14Map x := by
  change wordMap letterMap false (d06Letters ++ d09Letters) x = _
  rw [wordMap_append]
  rw [d06Map_correct h]
  rw [d09Map_correct h]
  exact (h.d14 x).symm

theorem vMap_correct_of_checks (hd : DictionaryChecks) (ho : OutputChecksA)
    (x : Fin 306936) : wordMap letterMap false vLetters x = vMap x := by
  rw [← wordMap_normalize vLetters x]
  change wordMap letterMap false [d14Letters, d05Letters, d09Letters, d09Letters, d11Letters, d12Letters, d10Letters, d09Letters, d10Letters, d13Letters, d08Letters, d04Letters, [0]].flatten x = _
  rw [wordMap_flatten]
  simp only [List.foldr_cons, List.foldr_nil, d04Map_correct hd, d05Map_correct hd, d08Map_correct hd, d09Map_correct hd, d10Map_correct hd, d11Map_correct hd, d12Map_correct hd, d13Map_correct hd, d14Map_correct hd]
  exact (ho.v x).symm

theorem rMap_correct_of_checks (hd : DictionaryChecks) (ho : OutputChecksA)
    (x : Fin 306936) : wordMap letterMap false rLetters x = rMap x := by
  rw [← wordMap_normalize rLetters x]
  change wordMap letterMap false [d12Letters, d13Letters, d07Letters, d05Letters, d09Letters, d07Letters, d11Letters, d07Letters, d13Letters, d12Letters, d11Letters, d08Letters, [0]].flatten x = _
  rw [wordMap_flatten]
  simp only [List.foldr_cons, List.foldr_nil, d05Map_correct hd, d07Map_correct hd, d08Map_correct hd, d09Map_correct hd, d11Map_correct hd, d12Map_correct hd, d13Map_correct hd]
  exact (ho.r x).symm

theorem wMap_correct_of_checks (hd : DictionaryChecks) (ho : OutputChecksA)
    (x : Fin 306936) : wordMap letterMap false wLetters x = wMap x := by
  rw [← wordMap_normalize wLetters x]
  change wordMap letterMap false [d10Letters, d09Letters, d11Letters, d14Letters, d09Letters, d14Letters, d11Letters, d14Letters, d06Letters, d07Letters, d08Letters, d04Letters].flatten x = _
  rw [wordMap_flatten]
  simp only [List.foldr_cons, List.foldr_nil, d04Map_correct hd, d06Map_correct hd, d07Map_correct hd, d08Map_correct hd, d09Map_correct hd, d10Map_correct hd, d11Map_correct hd, d14Map_correct hd]
  exact (ho.w x).symm

theorem uMap_correct_of_checks (hd : DictionaryChecks) (ho : OutputChecksB)
    (x : Fin 306936) : wordMap letterMap false uLetters x = uMap x := by
  rw [← wordMap_normalize uLetters x]
  change wordMap letterMap false [[3], d10Letters, d09Letters, d07Letters, d10Letters, d08Letters, d09Letters, d12Letters, d06Letters, d06Letters, d13Letters, [0]].flatten x = _
  rw [wordMap_flatten]
  simp only [List.foldr_cons, List.foldr_nil, d06Map_correct hd, d07Map_correct hd, d08Map_correct hd, d09Map_correct hd, d10Map_correct hd, d12Map_correct hd, d13Map_correct hd]
  exact (ho.u x).symm

theorem sMap_correct_of_checks (hd : DictionaryChecks) (ho : OutputChecksB)
    (x : Fin 306936) : wordMap letterMap false sLetters x = sMap x := by
  rw [← wordMap_normalize sLetters x]
  change wordMap letterMap false [[1], d11Letters, d11Letters, d10Letters, d10Letters, d12Letters, d09Letters, d07Letters, d05Letters, d09Letters, d09Letters, d08Letters, d04Letters].flatten x = _
  rw [wordMap_flatten]
  simp only [List.foldr_cons, List.foldr_nil, d04Map_correct hd, d05Map_correct hd, d07Map_correct hd, d08Map_correct hd, d09Map_correct hd, d10Map_correct hd, d11Map_correct hd, d12Map_correct hd]
  exact (ho.s x).symm

end Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables.WordChecks
