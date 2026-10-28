module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Data
import Mathlib.Tactic.FinCases

/-!
# Kernel checks for the HS involution certificates

Check the 512-row word tree and right multiplication transitions, a two-point
inverse to its enumeration, and a conjugating word for each involution. For
other rows a single moved point of the square excludes order two.
The identities refer to the actual ATLAS generators, with no external oracle.

Source: ATLAS HSG1-p100B0; GLS3 Table 5.3m.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Certificate
open Theory.GroupTheory Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

theorem localValue_spec : ∀ (s : Fin 4) (p : Fin 100),
    localValue s p = inclusion (localLetter s) p := by
  apply allFin
  decide +kernel

theorem ambientValue_spec : ∀ (s : Fin 3) (p : Fin 100),
    ambientValue s p = inclusion (ambientLetter s) p := by
  apply allFin
  decide +kernel

theorem wordValue_spec (w : List (Fin 3)) (p : Fin 100) :
    wordValue w p = inclusion (evalWord ambientLetter w) p := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    rw [wordValue, ih, ambientValue_spec]
    rfl

theorem localLetter_inv (s : Fin 4) :
    localLetter (invLetter s) = (localLetter s)⁻¹ := by
  apply inclusion_injective
  apply Equiv.ext
  apply allFin
  revert s
  apply allFin
  decide +kernel

theorem word_data : ∀ i : Fin 512, i ≠ 0 →
    (parent i).val < i.val ∧
    words i = words (parent i) ++ [parentLetter i] ∧
    next (parent i) (parentLetter i) = i := by
  apply allFin
  decide +kernel

theorem value_zero : ∀ p : Fin 100, value 0 p = p := by
  apply allFin
  decide +kernel

theorem steps_checked : checkFin (fun i : Fin 512 =>
    checkFin (fun s : Fin 4 => checkFin (fun p : Fin 100 => decide
      (value (next i s) p = value i (localValue s p))))) = true := by
  decide +kernel

theorem value_step (i : Fin 512) (s : Fin 4) (p : Fin 100) :
    value (next i s) p = value i (localValue s p) :=
  of_decide_eq_true (checkedAt (checkedAt (checkedAt steps_checked i) s) p)

theorem decode_value : ∀ i : Fin 512, decode (value i 1) (value i 4) = i := by
  apply allFin
  decide +kernel

theorem t_value : ∀ p : Fin 100, value 117 p = inclusion t p := by
  apply allFin
  decide +kernel

theorem baseValue_spec (i : Fin 512) (p : Fin 100) :
    baseValue i p = inclusion (base i) p := by
  by_cases h : fusionA i = true
  · simp only [baseValue, base, h, ↓reduceIte]
    rfl
  · simp only [baseValue, base, h, Bool.false_eq_true, ↓reduceIte]
    exact t_value p

theorem fusion_checked : checkFin (fun i : Fin 512 => decide (i ≠ 0 →
    value i (value i (badPoint i)) = badPoint i →
    checkFin (fun p : Fin 100 => decide
      (wordValue (fusionWord i) (value i p) =
        baseValue i (wordValue (fusionWord i) p))) = true)) = true := by
  decide +kernel

theorem fusion_value (i : Fin 512) (hi : i ≠ 0)
    (hsq : value i (value i (badPoint i)) = badPoint i) (p : Fin 100) :
    wordValue (fusionWord i) (value i p) =
      baseValue i (wordValue (fusionWord i) p) := by
  have h := of_decide_eq_true (checkedAt fusion_checked i)
  exact of_decide_eq_true (checkedAt (h hi hsq) p)

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Certificate
