module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.CommutatorCheck.Range
import Mathlib.Tactic.FinCases

/-!
# Certification of the accelerated J₂ word tables

First compare the three centralizer letters with their original words in
`a,b,b⁻¹`. Each packed row is then checked against its parent row and final
letter, and induction on the word spanning tree identifies it with the
published word. All point comparisons and word-tree metadata are reduced
in the kernel in bounded blocks. No enumeration coverage is used.
Source: ATLAS `J2G1-p100B0`; unchanged `OrbitData` and `CentralizerData` words.
-/

@[expose] public section
set_option Elab.async false
open Theory.GroupTheory
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck

/-- Evaluate the original alphabet using the previously certified packed lookup. -/
def wordValue : List (Fin 3) → Fin 100 → Fin 100
  | [], p => p
  | s :: w, p => letterValue s (wordValue w p)

theorem wordValue_eq (w : List (Fin 3)) (p : Fin 100) :
    wordValue w p = inclusion (evalWord letter w) p := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    simp only [wordValue, evalWord, map_mul, Equiv.Perm.mul_apply,
      inclusion_letter, ← letterValue_eq, ih]

def cWord : List (Fin 3) :=
  OrbitData.words 263 ++ [1] ++ (OrbitData.words 273).reverse.map invLetter

theorem cWord_eq : evalWord letter cWord = c := by
  have hn : OrbitData.next 263 1 = 273 := by decide +kernel
  simp only [cWord, evalWord_append, evalWord_reverse_map_inv letter invLetter letter_inv,
    evalWord, mul_one]
  simp only [c, schreier, hn, rep]

def localWord (s : Fin 3) : List (Fin 3) :=
  ![[0], cWord, cWord.reverse.map invLetter] s

theorem localWord_eq (s : Fin 3) : evalWord letter (localWord s) = centralizerLetter s := by
  fin_cases s
  · simp [localWord, centralizerLetter, letter]
  · exact cWord_eq
  · exact (evalWord_reverse_map_inv letter invLetter letter_inv cWord).trans
      (congrArg Inv.inv cWord_eq)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem localLetter_check : ∀ (s : Fin 3) (p : Fin 100),
    localLetterValue s p = wordValue (localWord s) p := by
  have hc : checkFin (fun s : Fin 3 => checkFin (fun p : Fin 100 =>
      decide (localLetterValue s p = wordValue (localWord s) p))) = true := by
    decide +kernel
  intro s
  apply allFin
  exact allFin (fun s : Fin 3 =>
    checkFin (fun p : Fin 100 => decide (localLetterValue s p = wordValue (localWord s) p)) = true)
    (by simpa only [Bool.decide_eq_true] using hc) s

theorem localLetterValue_eq (s : Fin 3) (p : Fin 100) :
    localLetterValue s p = inclusion (centralizerLetter s) p := by
  rw [localLetter_check, wordValue_eq, localWord_eq]


end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck

def centralCheck (i : Fin 1920) : Bool :=
  if i = 0 then checkFin (fun p : Fin 100 => decide (centralValue i p = p))
  else decide ((centralParent i).val < i.val ∧
      CentralizerData.words i = CentralizerData.words (centralParent i) ++ [centralLast i]) &&
    checkFin (fun p : Fin 100 => decide (centralValue i p =
      centralValue (centralParent i) (localLetterValue (centralLast i) p)))

def repCheck (i : Fin 315) : Bool :=
  if i = 0 then checkFin (fun p : Fin 100 => decide (repValue i p = p))
  else checkFin (fun p : Fin 100 => decide (repValue i p =
    repValue (OrbitData.parent i) (letterValue (OrbitData.parentLetter i) p)))

def comparisonCheck (i : Fin 1920) : Bool :=
  centralCheck i && if h : i.val < 315 then repCheck ⟨i.val, h⟩ else true

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck

namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block00 : checkRange comparisonCheck 0 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block01 : checkRange comparisonCheck 32 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block02 : checkRange comparisonCheck 64 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block03 : checkRange comparisonCheck 96 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block04 : checkRange comparisonCheck 128 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block05 : checkRange comparisonCheck 160 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block06 : checkRange comparisonCheck 192 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block07 : checkRange comparisonCheck 224 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block08 : checkRange comparisonCheck 256 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block09 : checkRange comparisonCheck 288 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block10 : checkRange comparisonCheck 320 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block11 : checkRange comparisonCheck 352 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block12 : checkRange comparisonCheck 384 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block13 : checkRange comparisonCheck 416 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block14 : checkRange comparisonCheck 448 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block15 : checkRange comparisonCheck 480 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block16 : checkRange comparisonCheck 512 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block17 : checkRange comparisonCheck 544 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block18 : checkRange comparisonCheck 576 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block19 : checkRange comparisonCheck 608 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block20 : checkRange comparisonCheck 640 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block21 : checkRange comparisonCheck 672 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block22 : checkRange comparisonCheck 704 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block23 : checkRange comparisonCheck 736 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block24 : checkRange comparisonCheck 768 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block25 : checkRange comparisonCheck 800 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block26 : checkRange comparisonCheck 832 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block27 : checkRange comparisonCheck 864 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block28 : checkRange comparisonCheck 896 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block29 : checkRange comparisonCheck 928 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block30 : checkRange comparisonCheck 960 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block31 : checkRange comparisonCheck 992 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block32 : checkRange comparisonCheck 1024 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block33 : checkRange comparisonCheck 1056 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block34 : checkRange comparisonCheck 1088 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block35 : checkRange comparisonCheck 1120 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block36 : checkRange comparisonCheck 1152 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block37 : checkRange comparisonCheck 1184 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block38 : checkRange comparisonCheck 1216 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block39 : checkRange comparisonCheck 1248 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block40 : checkRange comparisonCheck 1280 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block41 : checkRange comparisonCheck 1312 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block42 : checkRange comparisonCheck 1344 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block43 : checkRange comparisonCheck 1376 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block44 : checkRange comparisonCheck 1408 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block45 : checkRange comparisonCheck 1440 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block46 : checkRange comparisonCheck 1472 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block47 : checkRange comparisonCheck 1504 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block48 : checkRange comparisonCheck 1536 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block49 : checkRange comparisonCheck 1568 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block50 : checkRange comparisonCheck 1600 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block51 : checkRange comparisonCheck 1632 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block52 : checkRange comparisonCheck 1664 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block53 : checkRange comparisonCheck 1696 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block54 : checkRange comparisonCheck 1728 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block55 : checkRange comparisonCheck 1760 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block56 : checkRange comparisonCheck 1792 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block57 : checkRange comparisonCheck 1824 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block58 : checkRange comparisonCheck 1856 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem block59 : checkRange comparisonCheck 1888 32 = true := by
  decide +kernel

private theorem comparison_blocks (k : Fin 60) :
    checkRange comparisonCheck (k.val * 32) 32 = true := by
  fin_cases k
  · exact block00
  · exact block01
  · exact block02
  · exact block03
  · exact block04
  · exact block05
  · exact block06
  · exact block07
  · exact block08
  · exact block09
  · exact block10
  · exact block11
  · exact block12
  · exact block13
  · exact block14
  · exact block15
  · exact block16
  · exact block17
  · exact block18
  · exact block19
  · exact block20
  · exact block21
  · exact block22
  · exact block23
  · exact block24
  · exact block25
  · exact block26
  · exact block27
  · exact block28
  · exact block29
  · exact block30
  · exact block31
  · exact block32
  · exact block33
  · exact block34
  · exact block35
  · exact block36
  · exact block37
  · exact block38
  · exact block39
  · exact block40
  · exact block41
  · exact block42
  · exact block43
  · exact block44
  · exact block45
  · exact block46
  · exact block47
  · exact block48
  · exact block49
  · exact block50
  · exact block51
  · exact block52
  · exact block53
  · exact block54
  · exact block55
  · exact block56
  · exact block57
  · exact block58
  · exact block59

private theorem all_central (i : Fin 1920) : centralCheck i = true :=
  (Bool.and_eq_true_iff.mp (all_of_blocks comparisonCheck comparison_blocks i)).1

private theorem all_rep (i : Fin 315) : repCheck i = true := by
  have hi : i.val < 1920 := by omega
  have hh := (Bool.and_eq_true_iff.mp
    (all_of_blocks comparisonCheck comparison_blocks ⟨i.val, hi⟩)).2
  simpa only [dif_pos i.isLt] using hh

theorem central_word_data (i : Fin 1920) (hi : i ≠ 0) :
    (centralParent i).val < i.val ∧
    CentralizerData.words i =
      CentralizerData.words (centralParent i) ++ [centralLast i] := by
  have hh := all_central i
  rw [centralCheck, if_neg hi] at hh
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp hh).1

theorem rep_zero_check (p : Fin 100) : repValue 0 p = p := by
  have hh := all_rep 0
  rw [repCheck, if_pos rfl] at hh
  exact allFin _ hh p

theorem central_zero_check (p : Fin 100) : centralValue 0 p = p := by
  have hh := all_central 0
  rw [centralCheck, if_pos rfl] at hh
  exact allFin _ hh p

theorem rep_steps_check (i : Fin 315) (hi : i ≠ 0) (p : Fin 100) :
    repValue i p = repValue (OrbitData.parent i) (letterValue (OrbitData.parentLetter i) p) := by
  have hh := all_rep i
  rw [repCheck, if_neg hi] at hh
  exact allFin _ hh p

theorem central_steps_check (i : Fin 1920) (hi : i ≠ 0) (p : Fin 100) :
    centralValue i p = centralValue (centralParent i) (localLetterValue (centralLast i) p) := by
  have hh := all_central i
  rw [centralCheck, if_neg hi] at hh
  exact allFin _ (Bool.and_eq_true_iff.mp hh).2 p

theorem repValue_eq (i : Fin 315) (p : Fin 100) : repValue i p = inclusion (rep i) p := by
  have aux : ∀ (n : Nat) (j : Fin 315), j.val = n → ∀ q : Fin 100,
      repValue j q = inclusion (rep j) q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj q
      by_cases hzero : j = 0
      · subst j
        simpa only [rep_zero, map_one, Equiv.Perm.one_apply] using rep_zero_check q
      obtain ⟨hlt, hw, _⟩ := word_data j hzero
      have hp := ih (OrbitData.parent j).val (hj ▸ hlt) (OrbitData.parent j) rfl
      have hr : rep j = rep (OrbitData.parent j) * letter (OrbitData.parentLetter j) := by
        simp only [rep, hw, evalWord_append, evalWord, mul_one]
      rw [rep_steps_check j hzero, hp, hr, map_mul, Equiv.Perm.mul_apply,
        inclusion_letter, letterValue_eq]
  exact aux i.val i rfl p

theorem centralValue_eq (i : Fin 1920) (p : Fin 100) :
    centralValue i p = inclusion (centralizerElement i) p := by
  have aux : ∀ (n : Nat) (j : Fin 1920), j.val = n → ∀ q : Fin 100,
      centralValue j q = inclusion (centralizerElement j) q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj q
      by_cases hzero : j = 0
      · subst j
        exact central_zero_check q
      obtain ⟨hlt, hw⟩ := central_word_data j hzero
      have hp := ih (centralParent j).val (hj ▸ hlt) (centralParent j) rfl
      have hr : centralizerElement j =
          centralizerElement (centralParent j) * centralizerLetter (centralLast j) := by
        simp only [centralizerElement, hw, evalWord_append, evalWord, mul_one]
      rw [central_steps_check j hzero, hp, hr, map_mul, Equiv.Perm.mul_apply,
        localLetterValue_eq]
  exact aux i.val i rfl p

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck
