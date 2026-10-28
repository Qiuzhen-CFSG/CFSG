module

public import Theory.Mathieu.M22.Properties.CubicInverters.Data

/-!
# Kernel checks for M₂₂ cubic inverters

The checks connect every permutation table to a word in actual group elements.
A three-coordinate key separates all 256 local words. Every row is either the
identity, has nonidentity square, or inverts its designated cubic word. Thus the
finite certificate covers every local involution, without using class labels.

Source: the involution inversion step of Aschbacher–Smith H.12.1, printed p.394.
-/

public section
namespace Sporadic.Mathieu.M22CubicInverters
set_option maxRecDepth 100000

theorem letter_apply (j : Fin 3) (x : Fin 22) :
    (letter j).val x = letterTable j x := by
  revert j x
  decide +kernel

theorem innerWord_apply (w : List (Fin 3)) (x : Fin 22) :
    (innerWord w).val x = innerWordAction w x := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change (letter j).val ((innerWord w).val x) = _
    rw [letter_apply, ih]
    rfl

theorem generator_apply (i : Fin 4) (x : Fin 22) :
    (generator i).val x = generatorTable i x := by
  fin_cases i
  · change (innerWord (generatorWord 0)).val x = _
    rw [innerWord_apply]
    revert x
    decide +kernel
  · change (innerWord (generatorWord 1)).val x = _
    rw [innerWord_apply]
    revert x
    decide +kernel
  · change (innerWord (generatorWord 2)).val x = _
    rw [innerWord_apply]
    revert x
    decide +kernel
  · change m22OddPairSwap x = _
    revert x
    decide +kernel

theorem localWord_apply (w : List (Fin 4)) (x : Fin 22) :
    (localWord w).val x = localWordAction w x := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change (generator j).val ((localWord w).val x) = _
    rw [generator_apply, ih]
    rfl

theorem row_word_table (i : Fin 256) (x : Fin 22) :
    localWordAction (rowWord i) x = rowTable i x := by
  revert i x
  decide +kernel

theorem row_key_injective : Function.Injective (fun i : Fin 256 =>
    (rowTable i 0).val * 22 ^ 2 + (rowTable i 1).val * 22 + (rowTable i 4).val) := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

theorem cubic_word_table (i : Fin 58) (x : Fin 22) :
    innerWordAction (cubicWord i) x = cubicTable i x := by
  revert i x
  decide +kernel

theorem cubic_cube (i : Fin 58) (x : Fin 22) :
    cubicTable i (cubicTable i (cubicTable i x)) = x := by
  revert i x
  decide +kernel

theorem cubic_ne_one (i : Fin 58) :
    cubicTable i (cubicMovedPoint i) ≠ cubicMovedPoint i := by
  revert i
  decide +kernel

theorem row_cases (i : Fin 256) :
    (∀ x, rowTable i x = x) ∨
    (∃ x, rowTable i (rowTable i x) ≠ x) ∨
    (∀ x, rowTable i (cubicTable (witness i) (rowTable i x)) =
      cubicTable (witness i) (cubicTable (witness i) x)) := by
  revert i
  decide +kernel

end Sporadic.Mathieu.M22CubicInverters
