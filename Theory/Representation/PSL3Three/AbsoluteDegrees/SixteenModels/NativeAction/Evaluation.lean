module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Encoding
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Evaluation of the binary-polynomial matrix certificates

For a root `t⁴=t+1` in any characteristic-two field, the published coefficient
map preserves the encoded addition and multiplication. The addition proof uses
four binary coordinates instead of 256 symbolic polynomial cases. Multiplication
then follows from the sixteen multiplication-by-X identities. Evaluation thus
preserves the identity matrix and full matrix multiplication, in any universe.

This is the coefficient convention of the ATLAS data documented in
`SixteenModels.Data`; no representation-theoretic conclusion is assumed.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction

variable {F : Type*} [Field F] [CharP F 2]

private def bitCode : Fin 16 → Fin 4 → ZMod 2 :=
  ![![0, 0, 0, 0],
    ![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![1, 1, 0, 0],
    ![0, 0, 1, 0],
    ![1, 0, 1, 0],
    ![0, 1, 1, 0],
    ![1, 1, 1, 0],
    ![0, 0, 0, 1],
    ![1, 0, 0, 1],
    ![0, 1, 0, 1],
    ![1, 1, 0, 1],
    ![0, 0, 1, 1],
    ![1, 0, 1, 1],
    ![0, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem bitCode_add : ∀ a b : Fin 16, ∀ i : Fin 4,
    bitCode (addCode a b) i = bitCode a i + bitCode b i := by decide

private theorem coefficient_eq_bits (t : F) (a : Fin 16) :
    coefficient t a = ∑ i : Fin 4,
      (ZMod.castHom (dvd_refl 2) F) (bitCode a i) * t ^ i.val := by
  fin_cases a <;> simp [Fin.sum_univ_succ, coefficient, bitCode] <;> ring

theorem eval_add (t : F) (a b : Fin 16) :
    coefficient t (addCode a b) = coefficient t a + coefficient t b := by
  simp only [coefficient_eq_bits, bitCode_add, map_add, add_mul, Finset.sum_add_distrib]

theorem eval_shift (t : F) (ht : t ^ 4 = t + 1) (a : Fin 16) :
    coefficient t (shiftCode a) = t * coefficient t a := by
  fin_cases a <;> dsimp [shiftCode, coefficient] <;>
    ring_nf <;> (try rw [ht]) <;> (try ring_nf) <;> simp [CharTwo.two_eq_zero]

theorem eval_mul (t : F) (ht : t ^ 4 = t + 1) (a b : Fin 16) :
    coefficient t (mulCode a b) = coefficient t a * coefficient t b := by
  fin_cases b <;>
    simp only [mulCode, Matrix.cons_val_zero', Matrix.cons_val_succ',
      eval_add, eval_shift t ht] <;>
    simp only [coefficient, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring


@[expose] def evaluate (t : F) (A : CodeMatrix) : Matrix (Fin 16) (Fin 16) F :=
  A.map (coefficient t)

omit [CharP F 2] in
theorem evaluate_one (t : F) : evaluate t matrixOne = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [evaluate, matrixOne, Matrix.one_apply, hij, coefficient]

private theorem eval_sum (t : F) (xs : List (Fin 16)) :
    coefficient t (sumCode xs) = (xs.map (coefficient t)).sum := by
  induction xs with
  | nil => simp [sumCode, coefficient]
  | cons x xs ih => simp only [sumCode, eval_add, ih, List.map_cons, List.sum_cons]

theorem evaluate_mul (t : F) (ht : t ^ 4 = t + 1) (A B : CodeMatrix) :
    evaluate t (matrixMul A B) = evaluate t A * evaluate t B := by
  ext i j
  simp only [evaluate, Matrix.map_apply, matrixMul, eval_sum, List.map_ofFn,
    Function.comp_apply, eval_mul t ht, List.sum_ofFn, Matrix.mul_apply]

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction
