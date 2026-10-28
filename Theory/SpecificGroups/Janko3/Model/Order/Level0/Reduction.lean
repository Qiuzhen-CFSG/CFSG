module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0Data
import Mathlib.Tactic.FinCases

/-!
# Word reduction for the first J3 Schreier certificate

The relations A² = B³ = 1 normalize words in the signed ATLAS generators.
Equal normal forms prove transitions algebraically; remaining transitions are
checked on all 6156 letters using the certified packed permutations.
Adapted from `Tits/Atlas1600OrderLevel0Reduction.lean`; witnesses come from
ATLAS J3G1-p6156B0 and `Order/data/witnesses.json`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0
open Theory.GroupTheory
set_option maxRecDepth 100000
set_option Elab.async false

private def reducedGen (a b : Equiv.Perm (Fin 6156)) : Fin 3 → Equiv.Perm (Fin 6156)
  | 0 => a
  | 1 => b
  | 2 => b⁻¹

@[expose] public def push : Fin 3 → List (Fin 3) → List (Fin 3)
  | 0, 0 :: w => w
  | 1, 1 :: w => 2 :: w
  | 2, 2 :: w => 1 :: w
  | 1, 2 :: w => w
  | 2, 1 :: w => w
  | i, w => i :: w

private theorem genA_square : atlasA * atlasA = 1 := by
  simpa only [pow_two] using atlasA_sq

private theorem genB_cube : atlasB * atlasB * atlasB = 1 := by
  calc
    atlasB * atlasB * atlasB = atlasB ^ 3 := by simp [pow_succ, mul_assoc]
    _ = 1 := atlasB_cube

private theorem push_eval (a b : Equiv.Perm (Fin 6156))
    (ha : a * a = 1) (hb : b * b * b = 1) (i : Fin 3) (w : List (Fin 3)) :
    evalWord (reducedGen a b) (push i w) = reducedGen a b i * evalWord (reducedGen a b) w := by
  have hbinv : b⁻¹ = b * b := inv_eq_of_mul_eq_one_left hb
  cases w with
  | nil => fin_cases i <;> simp [push, evalWord, reducedGen]
  | cons j w =>
    fin_cases i <;> fin_cases j <;>
      simp [push, reducedGen, evalWord, ← mul_assoc, ha, hb, hbinv]

@[expose] public def normalize : List (Fin 3) → List (Fin 3)
  | [] => []
  | i :: w => push i (normalize w)

private theorem normalize_eval (w : List (Fin 3)) :
    evalWord (reducedGen atlasA atlasB) (normalize w) = evalWord (reducedGen atlasA atlasB) w := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [normalize, push_eval atlasA atlasB genA_square genB_cube, ih]

@[expose] public def reduceLetter : Fin 4 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 2

private theorem reducedGen_letter (i : Fin 4) :
    reducedGen atlasA atlasB (reduceLetter i) = L0Gen i := by
  have ha : atlasA⁻¹ = atlasA := inv_eq_of_mul_eq_one_left genA_square
  fin_cases i <;> simp [reduceLetter, reducedGen, L0Gen, ha]

private theorem reduceWord_eval (w : List (Fin 4)) :
    evalWord (reducedGen atlasA atlasB) (w.map reduceLetter) = evalWord L0Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons, evalWord, reducedGen_letter, ih]

@[expose] public def reducedWord (w : List (Fin 4)) : List (Fin 3) := normalize (w.map reduceLetter)

private theorem reducedWord_eval (w : List (Fin 4)) :
    evalWord (reducedGen atlasA atlasB) (reducedWord w) = evalWord L0Gen w := by
  rw [reducedWord, normalize_eval, reduceWord_eval]

@[expose] public def L1GenWord : Fin 4 → List (Fin 4)
  | 0 => L1G0Word
  | 1 => L1G1Word
  | 2 => L1G0Word.reverse.map L0Inv
  | 3 => L1G1Word.reverse.map L0Inv

@[expose] public def algebraic (i : Fin 4) (r : Fin 6156) : Prop :=
  reducedWord (i :: L0RepWord r) =
    reducedWord (L0RepWord (L0Act i r) ++ (L0Factor i r).flatMap L1GenWord)

private theorem expand_letter (i : Fin 4) :
    evalWord L0Gen (L1GenWord i) = L1Gen i := by
  have hinv : ∀ j, L0Gen (L0Inv j) = (L0Gen j)⁻¹ := L0Inv_spec
  fin_cases i
  · change evalWord L0Gen L1G0Word = L1G0
    exact L1G0_eq_word.symm
  · change evalWord L0Gen L1G1Word = L1G1
    exact L1G1_eq_word.symm
  · change evalWord L0Gen (L1G0Word.reverse.map L0Inv) = L1G0⁻¹
    calc
      evalWord L0Gen (L1G0Word.reverse.map L0Inv) = (evalWord L0Gen L1G0Word)⁻¹ :=
        evalWord_reverse_map_inv L0Gen L0Inv hinv L1G0Word
      _ = L1G0⁻¹ := congrArg Inv.inv L1G0_eq_word.symm
  · change evalWord L0Gen (L1G1Word.reverse.map L0Inv) = L1G1⁻¹
    calc
      evalWord L0Gen (L1G1Word.reverse.map L0Inv) = (evalWord L0Gen L1G1Word)⁻¹ :=
        evalWord_reverse_map_inv L0Gen L0Inv hinv L1G1Word
      _ = L1G1⁻¹ := congrArg Inv.inv L1G1_eq_word.symm

private theorem expand_eval (w : List (Fin 4)) :
    evalWord L0Gen (w.flatMap L1GenWord) = evalWord L1Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.flatMap_cons, evalWord_append, expand_letter, ih, evalWord]

public theorem algebraic_step (i : Fin 4) (r : Fin 6156) (h : algebraic i r) :
    L0Gen i * L0Rep r = L0Rep (L0Act i r) * evalWord L1Gen (L0Factor i r) := by
  have he := congrArg (evalWord (reducedGen atlasA atlasB)) h
  simpa only [reducedWord_eval, evalWord_append, expand_eval, L0Rep] using he

public instance (i : Fin 4) (r : Fin 6156) : Decidable (algebraic i r) :=
  inferInstanceAs (Decidable (_ = _))

@[expose] public def fastCheck (i : Fin 4) (r : Fin 6156) : Prop :=
  checkFin (fun x : Fin 6156 => decide (
    (fastL0Gen i * evalWord fastL0Gen (L0RepWord r)) x =
    (evalWord fastL0Gen (L0RepWord (L0Act i r)) * evalWord L1Gen (L0Factor i r)) x)) = true

public instance (i : Fin 4) (r : Fin 6156) : Decidable (fastCheck i r) :=
  inferInstanceAs (Decidable (_ = _))

public theorem step_of_check (i : Fin 4) (r : Fin 6156)
    (h : algebraic i r ∨ fastCheck i r) :
    L0Gen i * L0Rep r = L0Rep (L0Act i r) * evalWord L1Gen (L0Factor i r) := by
  rcases h with h | h
  · exact algebraic_step i r h
  · apply Equiv.ext
    have hh := allFin _ h
    simpa only [fastL0Gen_eq, L0Rep] using hh

end Sporadic.Janko3.OrderCertificate.Level0
