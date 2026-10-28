module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.CyclicReplay
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.PoolData
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.PoolWords
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric

/-!
# Assembly interface for the compressed mixed-word certificate

The recorded trace separates into a finite pool of literal word identities and
numeric checks of its 1,718,562 instructions. The two obligations are checked
independently and are decoded here into the exact existing cyclic checker;
`local_words_of_numeric` applies that checker to the three fixed max3 words.

This module supplies the complete concrete trace data and its three output
comparisons. The mixed-relations consumer remains conditional on this trace so
that the source theorem's assembly keeps its explicit hypotheses.
Source: ATLAS G23G1-P1 and G23G1-max3W1; see `Certificates/source/README.md`.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates
open Subgroup.CosetWordCertificate

/-! The numeric trace and the literal word pool are decoded only at this
interface.  The two independent certificate modules retain their packed
representations, while these definitions expose the exact replay data used by
`CyclicReplay`. -/

def traceDefinitions : Definitions Bool :=
  Pooled.definitions Numeric.definitionCode

def traceFacts (n : Nat) : CyclicReplay.Fact :=
  (Numeric.facts n).decode (pool PoolWords.word)

def traceInstructions (n : Nat) : CyclicReplay.Instruction :=
  (Numeric.instructions n).decode (pool PoolWords.word)

theorem traceChecked : ∀ n, n < traceLength →
    CyclicReplay.check traceDefinitions.parent traceDefinitions.letter traceFacts n
      (traceInstructions n) (traceFacts n) = true := by
  intro n hn
  apply Pooled.check_sound (pool PoolWords.word) PoolWords.valid Numeric.definitionCode
    Numeric.facts n (Numeric.instructions n) (Numeric.facts n)
  rw [check_pool_word]
  exact Numeric.checked n hn

theorem traceOutput_words : ∀ j, traceFacts (traceOutputs j) =
    ⟨0, reduce (Replay.expand boundLetters (localRelatorLetters (![3, 5, 6] j))), 0, 0⟩ := by
  intro j
  change (Numeric.facts (traceOutputs j)).decode (pool PoolWords.word) = _
  rw [Numeric.outputs j]
  change (⟨0, PoolWords.word (outputWordIndex j), 0, 0⟩ : CyclicReplay.Fact) = _
  rw [PoolWords.outputs j]

/-- Numeric certificates can be checked without loading any of the word data.
Their interpretation is restored here by the separately checked word pool. -/
theorem checkedTrace_of_numeric (words : Nat → Word Bool) (hw : Pooled.Valid (pool words))
    (d : Nat → Nat) (fs : Nat → Pooled.NumericFact) (ops : Nat → Pooled.NumericInstruction)
    (checked : ∀ n, n < traceLength →
      Pooled.check (pool (fun _ => [])) d fs n (ops n) (fs n) = true) :
    ∀ n, n < traceLength →
      CyclicReplay.check (Pooled.definitions d).parent (Pooled.definitions d).letter
        (fun k => (fs k).decode (pool words)) n ((ops n).decode (pool words))
        ((fs n).decode (pool words)) = true := by
  intro n hn
  apply Pooled.check_sound _ hw
  rw [check_pool_word words (fun _ => [])]
  exact checked n hn

/-- Actual consumer for precisely local indices 3, 5, 6. The source assumption
this discharges is the original mixed-relations branch; no local power contract
or permutation calculation is used. The finite checks remain explicit. -/
theorem local_words_of_numeric (words : Nat → Word Bool) (hw : Pooled.Valid (pool words))
    (d : Nat → Nat) (fs : Nat → Pooled.NumericFact) (ops : Nat → Pooled.NumericInstruction)
    (checked : ∀ n, n < traceLength →
      Pooled.check (pool (fun _ => [])) d fs n (ops n) (fs n) = true)
    (houtputs : ∀ j, fs (traceOutputs j) = ⟨0, outputWordIndex j, 0, 0⟩)
    (hwords : ∀ j, words (outputWordIndex j) =
      reduce (Replay.expand boundLetters (localRelatorLetters (![3, 5, 6] j)))) :
    ∀ j : Fin 3, eval boundGenerator (localRelatorLetters (![3, 5, 6] j)) = 1 := by
  intro j
  apply CyclicReplay.local_relation_of_checked_trace (Pooled.definitions d)
    (fun k => (fs k).decode (pool words)) (fun k => (ops k).decode (pool words))
    traceLength (checkedTrace_of_numeric words hw d fs ops checked)
    (![3, 5, 6] j) (traceOutputs j) (traceOutput_lt j)
  rw [houtputs j]
  change (⟨0, words (outputWordIndex j), 0, 0⟩ : CyclicReplay.Fact) = _
  rw [hwords j]

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates
