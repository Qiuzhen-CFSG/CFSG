module
public import Theory.SpecificGroups.Janko3.Model.Order.Level1Data
public import Theory.SpecificGroups.Janko3.Model.Order.Terminal
import Mathlib.Tactic.FinCases

/-!
# Word reduction for the second J3 Schreier certificate

The level-1 generators have orders dividing four and two. Reducing words in
these cyclic factors proves most transitions algebraically. The remaining
forward transitions are checked on bounded batches of letters. The already
certified order-sixteen subgroup certifies inverse factors, so inverse
transitions require no repeated checks on the 6156 letters.
Source: ATLAS J3G1-p6156B0, retained under `Model/data/`.
-/
namespace Sporadic.Janko3.OrderCertificate.Level1
open Theory.GroupTheory
set_option maxRecDepth 40000
set_option Elab.async false

set_option maxHeartbeats 4000000 in
private theorem a_four : L1G0 ^ 4 = 1 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel
set_option maxHeartbeats 4000000 in
private theorem b_two : L1G1 * L1G1 = 1 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private def reducedGen (a b : Equiv.Perm (Fin 6156)) (i : Fin 4) :
    Equiv.Perm (Fin 6156) := if i = 0 then b else a ^ i.val

@[expose] public def push (i : Fin 4) : List (Fin 4) → List (Fin 4)
  | [] => [i]
  | j :: w =>
    if i = 0 then (if j = 0 then w else i :: j :: w)
    else if j = 0 then i :: j :: w
    else if (i.val + j.val) % 4 = 0 then w
    else ⟨(i.val + j.val) % 4, Nat.mod_lt _ (by decide)⟩ :: w

private theorem push_eval (a b : Equiv.Perm (Fin 6156))
    (ha : a ^ 4 = 1) (hb : b * b = 1) (i : Fin 4) (w : List (Fin 4)) :
    evalWord (reducedGen a b) (push i w) =
      reducedGen a b i * evalWord (reducedGen a b) w := by
  have h4 : a * a * a * a = 1 := by simpa [pow_succ, ← mul_assoc] using ha
  cases w with
  | nil => simp [push, evalWord]
  | cons j w =>
    fin_cases i <;> fin_cases j <;>
      simp [push, reducedGen, evalWord, pow_succ, ← mul_assoc, h4, hb]



@[expose] public def normalize : List (Fin 4) → List (Fin 4)
  | [] => []
  | i :: w => push i (normalize w)

private theorem normalize_eval (a b : Equiv.Perm (Fin 6156))
    (ha : a ^ 4 = 1) (hb : b * b = 1) (w : List (Fin 4)) :
    evalWord (reducedGen a b) (normalize w) = evalWord (reducedGen a b) w := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [normalize, push_eval a b ha hb, ih]

@[expose] public def reduceLetter : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 0

private theorem reducedGen_letter (i : Fin 4) :
    reducedGen L1G0 L1G1 (reduceLetter i) = L1Gen i := by
  have ha : L1G0 ^ 3 = L1G0⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa only [← pow_succ] using a_four)
  have hb : L1G1 = L1G1⁻¹ := eq_inv_of_mul_eq_one_left b_two
  fin_cases i <;> simp [reduceLetter, reducedGen, L1Gen, ha, ← hb]

@[expose] public def reducedWord (w : List (Fin 4)) : List (Fin 4) :=
  normalize (w.map reduceLetter)

private theorem reducedWord_eval (w : List (Fin 4)) :
    evalWord (reducedGen L1G0 L1G1) (reducedWord w) = evalWord L1Gen w := by
  rw [reducedWord, normalize_eval _ _ a_four b_two]
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons, evalWord, reducedGen_letter, ih]

@[expose] public def genWord : Fin 6 → List (Fin 4)
  | 0 => L2G0Word
  | 1 => L2G1Word
  | 2 => L2G2Word
  | 3 => L2G0Word.reverse.map L1Inv
  | 4 => L2G1Word.reverse.map L1Inv
  | 5 => L2G2Word.reverse.map L1Inv

private theorem genWord_eval (i : Fin 6) : evalWord L1Gen (genWord i) = L2Gen i := by
  fin_cases i <;> simp only [genWord, L2Gen, ← L2G0_eq_word,
    ← L2G1_eq_word, ← L2G2_eq_word,
    evalWord_reverse_map_inv L1Gen L1Inv L1Inv_spec]

private theorem expand_eval (w : List (Fin 6)) :
    evalWord L1Gen (w.flatMap genWord) = evalWord L2Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.flatMap_cons, evalWord_append, genWord_eval, ih, evalWord]

@[expose] public def algebraic (i : Fin 4) (r : Fin 510) : Prop :=
  reducedWord (i :: L1RepWord r) =
    reducedWord (L1RepWord (L1Act i r) ++ (L1Factor i r).flatMap genWord)

public instance (i : Fin 4) (r : Fin 510) : Decidable (algebraic i r) :=
  inferInstanceAs (Decidable (_ = _))

public theorem algebraic_step (i : Fin 4) (r : Fin 510) (h : algebraic i r) :
    L1Gen i * L1Rep r = L1Rep (L1Act i r) * evalWord L2Gen (L1Factor i r) := by
  have he := congrArg (evalWord (reducedGen L1G0 L1G1)) h
  simpa only [reducedWord_eval, evalWord_append, expand_eval, evalWord, L1Rep] using he

@[expose] public def terminalIndex : List (Fin 6) → Fin 16
  | [] => 0
  | i :: w => L2Act i (terminalIndex w)

public theorem terminalIndex_eval (w : List (Fin 6)) :
    evalWord L2Gen w = L2Rep (terminalIndex w) := by
  induction w with
  | nil => exact L2Rep_base.symm
  | cons i w ih => rw [evalWord, ih, terminalIndex, L2Step]

set_option maxHeartbeats 4000000 in
private theorem inverse_data : ∀ (i : Fin 2) (r : Fin 510),
    let j := i.castLE (by decide : 2 ≤ 4)
    let s := L1Act (L1Inv j) r
    L1Act j s = r ∧ terminalIndex (L1Factor j s ++ L1Factor (L1Inv j) r) = 0 := by
  apply allFin₂
  decide +kernel

/-- The published inverse factors agree with the certified forward transitions. -/
public theorem step_of_forward
    (h : ∀ (i : Fin 2) (r : Fin 510),
      let j := i.castLE (by decide : 2 ≤ 4)
      L1Gen j * L1Rep r = L1Rep (L1Act j r) * evalWord L2Gen (L1Factor j r))
    (i : Fin 4) (r : Fin 510) :
    L1Gen i * L1Rep r = L1Rep (L1Act i r) * evalWord L2Gen (L1Factor i r) := by
  have hinv (k : Fin 2) :
      let j := k.castLE (by decide : 2 ≤ 4)
      L1Gen (L1Inv j) * L1Rep r =
        L1Rep (L1Act (L1Inv j) r) * evalWord L2Gen (L1Factor (L1Inv j) r) := by
    let j := k.castLE (by decide : 2 ≤ 4)
    let s := L1Act (L1Inv j) r
    obtain ⟨hact, hidx⟩ := inverse_data k r
    have hfactor : evalWord L2Gen (L1Factor j s) *
        evalWord L2Gen (L1Factor (L1Inv j) r) = 1 := by
      rw [← evalWord_append, terminalIndex_eval, hidx, L2Rep_base]
    have hf := h k s
    dsimp only at hf
    rw [hact] at hf
    change L1Gen j * L1Rep s = L1Rep r * evalWord L2Gen (L1Factor j s) at hf
    dsimp only
    rw [L1Inv_spec]
    calc
      (L1Gen j)⁻¹ * L1Rep r =
          (L1Gen j)⁻¹ * (L1Rep r *
            (evalWord L2Gen (L1Factor j s) *
              evalWord L2Gen (L1Factor (L1Inv j) r))) := by rw [hfactor, mul_one]
      _ = (L1Gen j)⁻¹ * ((L1Rep r * evalWord L2Gen (L1Factor j s)) *
          evalWord L2Gen (L1Factor (L1Inv j) r)) := by rw [mul_assoc]
      _ = L1Rep s * evalWord L2Gen (L1Factor (L1Inv j) r) := by
        rw [← hf]
        simp only [← mul_assoc, inv_mul_cancel, one_mul]
  fin_cases i
  · exact h 0 r
  · exact h 1 r
  · exact hinv 0
  · exact hinv 1

end Sporadic.Janko3.OrderCertificate.Level1
