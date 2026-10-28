module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Arithmetic for the degree-36 Hall--Janko certificate

Packed binary product checks and entrywise scalar transport certify expressions,
rank-one matrices and orbit columns over every characteristic-two field.
Expressions use only the two generators, one, addition and multiplication, so
their values belong to the generated algebra. The concrete consumer is the
ATLAS `J2G1-f2r36B0` candidate; see the parent `source/README.md`.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.ThirtySix
open Thompson.BinaryMatrix

inductive Expr where
  | one | a | b
  | add (x y : Expr)
  | mul (x y : Expr)

def Expr.eval {R : Type*} [Semiring R] (A B : R) : Expr → R
  | .one => 1
  | .a => A
  | .b => B
  | .add x y => x.eval A B + y.eval A B
  | .mul x y => x.eval A B * y.eval A B

theorem Expr.mem {F R : Type*} [Field F] [Ring R] [Algebra F R]
    (A B : R) (e : Expr) : e.eval A B ∈ Algebra.adjoin F ({A, B} : Set R) := by
  induction e with
  | one => exact (Algebra.adjoin F _).one_mem
  | a => exact Algebra.subset_adjoin (by simp [Expr.eval])
  | b => exact Algebra.subset_adjoin (by simp [Expr.eval])
  | add x y hx hy => exact (Algebra.adjoin F _).add_mem hx hy
  | mul x y hx hy => exact (Algebra.adjoin F _).mul_mem hx hy

def checkSum (n : ℕ) (a b c : Array ℕ) : Bool :=
  (List.range n).all fun i => a[i]! ^^^ b[i]! == c[i]!

theorem checkSum_sound (n : ℕ) (a b c : Array ℕ)
    (h : checkSum n a b c = true) : decode n a + decode n b = decode n c := by
  ext i j
  have hi : a[i.val]! ^^^ b[i.val]! = c[i.val]! :=
    of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  change bit a[i.val]! j.val + bit b[i.val]! j.val = bit c[i.val]! j.val
  rw [← bit_xor, hi]

variable (F : Type*) [Field F] [CharP F 2]

theorem eval_sum (n : ℕ) (a b c : Array ℕ)
    (h : decode n a + decode n b = decode n c) :
    Binary.eval F n a + Binary.eval F n b = Binary.eval F n c := by
  have hm := congrArg ((ZMod.castHom (dvd_refl 2) F).mapMatrix (m := Fin n)) h
  simpa only [map_add, Binary.eval] using hm

theorem eval_one (n : ℕ) (a : Array ℕ) (h : decode n a = 1) :
    Binary.eval F n a = 1 := by
  have hm := congrArg ((ZMod.castHom (dvd_refl 2) F).mapMatrix (m := Fin n)) h
  simpa only [map_one, Binary.eval] using hm

theorem eval_column (n : ℕ) (a b : Array ℕ) (j k : Fin n)
    (h : (fun i => decode n a i j) = (fun i => decode n b i k)) :
    (fun i => Binary.eval F n a i j) = (fun i => Binary.eval F n b i k) := by
  funext i
  exact congrArg (ZMod.castHom (dvd_refl 2) F) (congrFun h i)

theorem eval_row (n : ℕ) (a b : Array ℕ) (j k : Fin n)
    (h : decode n a j = decode n b k) :
    Binary.eval F n a j = Binary.eval F n b k := by
  funext i
  exact congrArg (ZMod.castHom (dvd_refl 2) F) (congrFun h i)

theorem eval_outer (n : ℕ) (r v l : Array ℕ) (j : Fin n)
    (h : decode n r = Matrix.vecMulVec (fun i => decode n v i j) (decode n l j)) :
    Binary.eval F n r =
      Matrix.vecMulVec (fun i => Binary.eval F n v i j) (Binary.eval F n l j) := by
  ext i k
  have hm := congrArg (ZMod.castHom (dvd_refl 2) F) (congrFun (congrFun h i) k)
  simpa only [Binary.eval, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.vecMulVec, Matrix.of_apply, map_mul] using hm

omit [CharP F 2] in
theorem column_product {n : ℕ} (a b c : Matrix (Fin n) (Fin n) F)
    (h : a * b = c) (j : Fin n) :
    a.mulVec (fun k => b k j) = fun k => c k j := by
  funext i
  exact congrFun (congrFun h i) j

omit [CharP F 2] in
theorem row_product {n : ℕ} (a b c : Matrix (Fin n) (Fin n) F)
    (h : a * b = c) (j : Fin n) : Matrix.vecMul (a j) b = c j := by
  funext i
  exact congrFun (congrFun h j) i

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.ThirtySix
