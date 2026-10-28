module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.Mask
public import Mathlib.Data.Matrix.Mul

/-!
# Matrices of binary linear forms

Each entry is a mask representing a linear form in a common family of binary
coordinates. Xor addition and multiplication by concrete binary matrices commute
with evaluation, including for rectangular matrices.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.MaskMatrices

/-- A rectangular matrix of binary linear forms in `n` coordinates. -/
abbrev MatrixMask (r c n : ℕ) := Fin r → Fin c → BitVec n

/-- Decode concrete binary rows as a matrix over the field of two elements. -/
def decode {r c : ℕ} (a : Fin r → BitVec c) : Matrix (Fin r) (Fin c) (ZMod 2) :=
  fun i j => if (a i).getLsbD j.val then 1 else 0

/-- Evaluate every entry of a matrix of linear forms at the same coordinates. -/
def evaluate {r c n : ℕ} (d : Fin n → ZMod 2) (M : MatrixMask r c n) :
    Matrix (Fin r) (Fin c) (ZMod 2) :=
  fun i j => Mask.evalRow d (M i j)

theorem evaluate_zero {r c n : ℕ} (d : Fin n → ZMod 2) :
    evaluate d (0 : MatrixMask r c n) = 0 := by
  funext i j
  exact Mask.evalRow_zero d

/-- Add symbolic matrices by taking the xor of corresponding masks. -/
def add {r c n : ℕ} (M N : MatrixMask r c n) : MatrixMask r c n :=
  fun i j => M i j ^^^ N i j

theorem evaluate_add {r c n : ℕ} (d : Fin n → ZMod 2) (M N : MatrixMask r c n) :
    evaluate d (add M N) = evaluate d M + evaluate d N := by
  funext i j
  exact Mask.evalRow_xor d (M i j) (N i j)

/-- Multiply a symbolic matrix on the left by concrete binary rows. -/
def left {r k c n : ℕ} (a : Fin r → BitVec k) (M : MatrixMask k c n) :
    MatrixMask r c n :=
  fun i j => Mask.substitute (fun t => M t j) (a i)

theorem evaluate_left {r k c n : ℕ} (d : Fin n → ZMod 2)
    (a : Fin r → BitVec k) (M : MatrixMask k c n) :
    evaluate d (left a M) = decode a * evaluate d M := by
  funext i j
  change Mask.evalRow d (Mask.substitute (fun t => M t j) (a i)) = _
  rw [Mask.evalRow_substitute]
  simp only [Mask.evalRow, Matrix.mul_apply, decode, evaluate]
  apply Finset.sum_congr rfl
  intro t _
  cases (a i).getLsbD t.val <;> simp

/-- Multiply a symbolic matrix on the right by concrete binary rows. -/
def right {r k c n : ℕ} (M : MatrixMask r k n) (a : Fin k → BitVec c) :
    MatrixMask r c n :=
  fun i j => Mask.sum (fun t => if (a t).getLsbD j.val then M i t else 0)

theorem evaluate_right {r k c n : ℕ} (d : Fin n → ZMod 2)
    (M : MatrixMask r k n) (a : Fin k → BitVec c) :
    evaluate d (right M a) = evaluate d M * decode a := by
  funext i j
  simp only [evaluate, right, Mask.evalRow_sum, Matrix.mul_apply, decode]
  apply Finset.sum_congr rfl
  intro t _
  cases (a t).getLsbD j.val
  · simp only [Bool.false_eq_true, if_false, mul_zero]
    exact Mask.evalRow_zero d
  · simp

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.MaskMatrices
