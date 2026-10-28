module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.Chart
public import Mathlib.LinearAlgebra.Matrix.Trace

/-! Kernel-checked binary arithmetic for the scalar reconstruction certificate.
The parity fold and row products are proved to equal finite-field sums and
matrix multiplication. Source conventions: `../source/README.md`. -/

open scoped Matrix
open Janko4.GeneratorCertificates
@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate

def foldParity : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => foldParity k (x ^^^ (x >>> 2 ^ k))

theorem bit_shift (x k i : ℕ) : bit (x >>> k) i = bit x (k + i) := by
  simp [bit, Nat.testBit_shiftRight]

theorem foldParity_spec (k x i : ℕ) :
    bit (foldParity k x) i = ∑ j ∈ Finset.range (2 ^ k), bit x (i + j) := by
  induction k generalizing x with
  | zero => simp only [foldParity, pow_zero, Finset.sum_range_one, Nat.add_zero]
  | succ k ih =>
    rw [foldParity, ih]
    simp_rw [bit_xor, bit_shift]
    rw [Finset.sum_add_distrib, pow_succ, Nat.mul_two, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    omega

theorem parity_sum {n k : ℕ} (x : ℕ) (h : x < 2 ^ n) (hn : n ≤ 2 ^ k) :
    bit (foldParity k x) 0 = ∑ i : Fin n, bit x i.val := by
  rw [foldParity_spec, Fin.sum_univ_eq_sum_range]
  simp only [zero_add]
  symm
  apply Finset.sum_subset (Finset.range_mono hn)
  intro i _ hi
  have hni : n ≤ i := by simpa using hi
  have ht : x.testBit i = false := Nat.testBit_lt_two_pow
    (h.trans_le (Nat.pow_le_pow_right (by decide) hni))
  simp [bit, ht]

def pairing {m n : ℕ} (F R : Matrix (Fin m) (Fin n) (ZMod 2)) : ZMod 2 :=
  ∑ i, ∑ j, F i j * R i j

theorem pairing_trace {m n : ℕ} (F R : Matrix (Fin m) (Fin n) (ZMod 2)) :
    pairing F R = Matrix.trace (Fᵀ * R) := by
  simp only [pairing, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem pairing_mul_right {m n p : ℕ}
    (F : Matrix (Fin m) (Fin p) (ZMod 2))
    (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (B : Matrix (Fin n) (Fin p) (ZMod 2)) :
    pairing F (A * B) = pairing (Aᵀ * F) B := by
  simp only [pairing_trace, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

theorem pairing_mul_left {m n p : ℕ}
    (F : Matrix (Fin m) (Fin p) (ZMod 2))
    (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (B : Matrix (Fin n) (Fin p) (ZMod 2)) :
    pairing F (A * B) = pairing (F * Bᵀ) A := by
  simp only [pairing_trace, Matrix.transpose_mul, Matrix.transpose_transpose]
  simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle Fᵀ A B)

def functional {m n : ℕ} (F : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Matrix (Fin m) (Fin n) (ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun := pairing F
  map_add' X Y := by simp [pairing, mul_add, Finset.sum_add_distrib]
  map_smul' c X := by simp [pairing, Finset.mul_sum, mul_left_comm]

theorem pairing_add_left {m n : ℕ} (F G R : Matrix (Fin m) (Fin n) (ZMod 2)) :
    pairing (F + G) R = pairing F R + pairing G R := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

def decode {m n : ℕ} (x : ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit x (n * i.val + j.val)

theorem pairing_decode {m n k : ℕ} (x y : ℕ) (h : x &&& y < 2 ^ (m * n))
    (hn : m * n ≤ 2 ^ k) :
    pairing (decode x : Matrix (Fin m) (Fin n) (ZMod 2)) (decode y) =
      bit (foldParity k (x &&& y)) 0 := by
  rw [parity_sum _ h hn]
  rw [← (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change bit x (n * i.val + j.val) * bit y (n * i.val + j.val) =
    bit (x &&& y) (j.val + n * i.val)
  rw [Nat.add_comm j.val]
  simp only [bit, Nat.testBit_and]
  cases x.testBit (n * i.val + j.val) <;>
    cases y.testBit (n * i.val + j.val) <;> decide

def rows {m n : ℕ} (x : ℕ) : Vector ℕ m :=
  Vector.ofFn (fun i => (x >>> (n * i.val)) % 2 ^ n)

def decodeRows {m : ℕ} (n : ℕ) (xs : Vector ℕ m) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit (xs.get i) j.val

theorem decode_rows {m n : ℕ} (x : ℕ) : decodeRows n (rows (m := m) (n := n) x) = decode x := by
  funext i j
  simp only [decodeRows, rows, get_ofFn, decode, bit, Nat.testBit_mod_two_pow,
    j.isLt, decide_true, Bool.true_and, Nat.testBit_shiftRight]


def rowProduct {n : ℕ} (x : ℕ) (ys : Vector ℕ n) : ℕ :=
  xorList (List.ofFn (fun i : Fin n => if x.testBit i.val then ys.get i else 0))

theorem decodeRows_product {m n p : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n)
    (zs : Vector ℕ m) (h : ∀ i, rowProduct (xs.get i) ys = zs.get i) :
    decodeRows n xs * decodeRows p ys = decodeRows p zs := by
  funext i j
  rw [Matrix.mul_apply]
  change (∑ a, bit (xs.get i) a.val * bit (ys.get a) j.val) = bit (zs.get i) j.val
  rw [← h i, rowProduct, bit_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro a _
  simp only [bit]
  cases h : (xs.get i).testBit a.val <;> simp [h]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate
