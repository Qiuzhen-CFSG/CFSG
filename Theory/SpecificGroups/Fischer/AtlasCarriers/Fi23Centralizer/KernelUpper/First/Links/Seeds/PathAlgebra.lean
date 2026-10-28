module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Seeds.Basic

/-!
# Checked tree paths identify the actual Fi23 representatives

A path using first-generator tree edges and non-loop second-generator edges
has trivial Schreier factor. Its chronological word therefore equals the
literal representative at its endpoint when it starts at the fixed root 1.
This gives short finite comparisons for the eleven shared-program outputs.

Source: ATLAS F23G1-p31671B0; the unchanged first Schreier tree used for GLS3
Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links.Seeds
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

def treeStep (s : Fin 3) (x : Fin 31671) : Bool :=
  if s = 0 then aTree x else if s = 1 then decide (sourceB x ≠ x) else false

def treePath : List (Fin 3) → Fin 31671 → Bool
  | [], _ => true
  | s :: w, x => treeStep s x && treePath w (symbolMap s x)

theorem treeStep_transition (s : Fin 3) (x : Fin 31671) (h : treeStep s x = true) :
    symbol s * representative x = representative (symbolMap s x) := by
  by_cases h0 : s = 0
  · simp only [treeStep, if_pos h0] at h
    simpa only [symbol, symbolMap, if_pos h0, ← generatorA_apply_eq_sourceA]
      using a_tree_transition x h
  · by_cases h1 : s = 1
    · simp only [treeStep, if_neg h0, if_pos h1, decide_eq_true_eq] at h
      simpa only [symbol, symbolMap, if_neg h0, if_pos h1,
        ← generatorB_apply_eq_sourceB] using
        b_transition x (by simpa only [generatorB_apply_eq_sourceB] using h)
    · simp only [treeStep, if_neg h0, if_neg h1, Bool.false_eq_true] at h

theorem treePath_transition (w : List (Fin 3)) (x : Fin 31671)
    (h : treePath w x = true) :
    wordValue w * representative x = representative (wordRun w x) := by
  induction w generalizing x with
  | nil => simp only [wordValue, one_mul, wordRun]
  | cons s w ih =>
    simp only [treePath, Bool.and_eq_true] at h
    rw [wordValue, mul_assoc, treeStep_transition s x h.1, ih _ h.2, wordRun]

theorem wordValue_eq_representative (w : List (Fin 3))
    (h : treePath w 1 = true) : wordValue w = representative (wordRun w 1) := by
  simpa only [representative_one, mul_one] using treePath_transition w 1 h

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links.Seeds
