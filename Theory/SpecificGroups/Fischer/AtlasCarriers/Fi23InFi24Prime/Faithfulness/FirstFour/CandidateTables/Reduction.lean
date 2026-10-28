module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.CandidateTables.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.PackedData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordEvaluation

/-!
# Full-ambient assembly from short word and composition certificates

Five forward word comparisons, four auxiliary inverse laws, and short
addition-chain steps imply both literal candidate-table comparisons. Every
quantifier ranges over the entire ambient set. Inverse words follow by
cancelling signed letters; the thirtieth and sixth powers follow by adding
iteration lengths. No comparison with the cycle-decoded generators is needed.

The numerical records below specify intermediate checks, not source theorems.
Their unconditional construction and the five forward word comparisons remain
separate obligations. The signed-letter cancellation is shared with
`Comparison.AmbientActions.WordChecks.InverseChecks`.
Source: `WordSetup`, `WordEvaluation`, ATLAS F24G1-p306936B0, GLS3 Table 5.3v.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables
open Certificate.Ambient

/-- The four auxiliary inverse witnesses on all ambient letters. -/
structure InverseChecks : Prop where
  u : ∀ x, uMap (uInvMap x) = x
  v : ∀ x, vMap (vInvMap x) = x
  w : ∀ x, wMap (wInvMap x) = x
  s : ∀ x, sMap (sInvMap x) = x

/-- Only short compositions occur in the thirtieth-power certificate. -/
structure PowerChecksA : Prop where
  base : ∀ x, a1Map x = wInvMap (rMap (vInvMap x))
  two : ∀ x, a2Map x = a1Map (a1Map x)
  three : ∀ x, a3Map x = a2Map (a1Map x)
  five : ∀ x, a5Map x = a3Map (a2Map x)
  ten : ∀ x, a10Map x = a5Map (a5Map x)
  fifteen : ∀ x, a15Map x = a10Map (a5Map x)
  output : ∀ x, FirstFourModel.imageA x = a15Map (a15Map x)

/-- The sixth-power steps and the literal conjugation for the second candidate. -/
structure PowerChecksB : Prop where
  base : ∀ x, b1Map x = uInvMap (vMap (vMap x))
  two : ∀ x, b2Map x = b1Map (b1Map x)
  three : ∀ x, b3Map x = b2Map (b1Map x)
  six : ∀ x, b6Map x = b3Map (b3Map x)
  output : ∀ x, FirstFourModel.imageB x =
    uMap (sMap (wMap (b6Map (wInvMap (sInvMap (uInvMap x))))))

/-- Split a forward word at any staged composition boundary. -/
theorem wordMap_append (ls ts : List (Fin 4)) (x : Fin 306936) :
    wordMap letterMap false (ls ++ ts) x =
      wordMap letterMap false ls (wordMap letterMap false ts x) := by
  induction ls with
  | nil => rfl
  | cons c cs ih =>
    change letterMap c (wordMap letterMap false (cs ++ ts) x) = _
    rw [ih]
    rfl

/-- Cancellation is purely numerical and does not assume generator agreement. -/
theorem wordMap_inverse_forward
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (ls : List (Fin 4)) (x : Fin 306936) :
    wordMap letterMap true ls (wordMap letterMap false ls x) = x := by
  induction ls with
  | nil => rfl
  | cons c cs ih =>
    change wordMap letterMap true cs
      (letterMap (inverseLetter c) (letterMap c (wordMap letterMap false cs x))) = x
    rw [hinv, ih]

/-- A checked inverse table supplies the inverse of a checked forward word. -/
theorem wordMap_inverse_of_forward
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (ls : List (Fin 4)) (f g : Fin 306936 → Fin 306936)
    (hfg : ∀ x, f (g x) = x)
    (hf : ∀ x, wordMap letterMap false ls x = f x) (x : Fin 306936) :
    wordMap letterMap true ls x = g x := by
  have h := hf (g x)
  rw [hfg] at h
  calc
    wordMap letterMap true ls x =
        wordMap letterMap true ls (wordMap letterMap false ls (g x)) :=
      congrArg (wordMap letterMap true ls) h.symm
    _ = g x := wordMap_inverse_forward hinv ls (g x)

/-- Addition of iteration lengths, with the same action order as WordEvaluation. -/
theorem iterateMap_add (f : Fin 306936 → Fin 306936) (k l : Nat) (x : Fin 306936) :
    iterateMap f (k + l) x = iterateMap f k (iterateMap f l x) := by
  induction k with
  | zero => simp only [Nat.zero_add, iterateMap]
  | succ k ih => simp only [Nat.succ_add, iterateMap, ih]

/-- The seven local A checks certify the complete thirtieth power. -/
theorem PowerChecksA.imageA_eq_iterate (h : PowerChecksA) (x : Fin 306936) :
    FirstFourModel.imageA x = iterateMap a1Map 30 x := by
  have h2 (y) : a2Map y = iterateMap a1Map 2 y := by rw [h.two]; rfl
  have h3 (y) : a3Map y = iterateMap a1Map 3 y := by
    rw [h.three, h2]
    rfl
  have h5 (y) : a5Map y = iterateMap a1Map 5 y := by
    rw [h.five, h3, h2, ← iterateMap_add]
  have h10 (y) : a10Map y = iterateMap a1Map 10 y := by
    rw [h.ten, h5, h5, ← iterateMap_add]
  have h15 (y) : a15Map y = iterateMap a1Map 15 y := by
    rw [h.fifteen, h10, h5, ← iterateMap_add]
  rw [h.output, h15, h15, ← iterateMap_add]

/-- The three doubling/addition steps certify the complete sixth power. -/
theorem PowerChecksB.b6_eq_iterate (h : PowerChecksB) (x : Fin 306936) :
    b6Map x = iterateMap b1Map 6 x := by
  have h2 (y) : b2Map y = iterateMap b1Map 2 y := by rw [h.two]; rfl
  have h3 (y) : b3Map y = iterateMap b1Map 3 y := by
    rw [h.three, h2]
    rfl
  rw [h.six, h3, h3, ← iterateMap_add]

/-- Exact full-domain first candidate assembly; no relabeling occurs. -/
theorem candidateAMap_eq_imageA_of_stages
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hi : InverseChecks) (ha : PowerChecksA)
    (hv : ∀ x, wordMap letterMap false vLetters x = vMap x)
    (hr : ∀ x, wordMap letterMap false rLetters x = rMap x)
    (hw : ∀ x, wordMap letterMap false wLetters x = wMap x)
    (x : Fin 306936) : candidateAMap x = FirstFourModel.imageA x := by
  have hvi := funext (wordMap_inverse_of_forward hinv vLetters vMap vInvMap hi.v hv)
  have hwi := funext (wordMap_inverse_of_forward hinv wLetters wMap wInvMap hi.w hw)
  unfold candidateAMap candidateAMapWith
  rw [hvi, funext hr, hwi, ← funext ha.base]
  exact (ha.imageA_eq_iterate x).symm

/-- Exact full-domain second candidate assembly, including both conjugating sides. -/
theorem candidateBMap_eq_imageB_of_stages
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hi : InverseChecks) (hb : PowerChecksB)
    (hu : ∀ x, wordMap letterMap false uLetters x = uMap x)
    (hv : ∀ x, wordMap letterMap false vLetters x = vMap x)
    (hw : ∀ x, wordMap letterMap false wLetters x = wMap x)
    (hs : ∀ x, wordMap letterMap false sLetters x = sMap x)
    (x : Fin 306936) : candidateBMap x = FirstFourModel.imageB x := by
  have hui := funext (wordMap_inverse_of_forward hinv uLetters uMap uInvMap hi.u hu)
  have hwi := funext (wordMap_inverse_of_forward hinv wLetters wMap wInvMap hi.w hw)
  have hsi := funext (wordMap_inverse_of_forward hinv sLetters sMap sInvMap hi.s hs)
  unfold candidateBMap candidateBMapWith
  rw [funext hu, funext hs, funext hw, hui, funext hv, hwi, hsi, ← funext hb.base,
    ← funext hb.b6_eq_iterate]
  exact (hb.output x).symm

end Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables
