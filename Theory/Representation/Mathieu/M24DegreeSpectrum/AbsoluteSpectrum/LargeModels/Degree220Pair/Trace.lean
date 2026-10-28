module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Data
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Checked binary traces separating the two degree-220 pairs

For each pair the trace of the product is the sum of the diagonal entries.
The packed checker computes each product row by XOR and accumulates its
specified diagonal bit. Induction proves that this is exactly the matrix
trace over `ZMod 2`; the two concrete values are checked by kernel reduction.
Transposition reverses the product, and cyclic invariance of trace supplies
the same values for the exported column-action matrices.

No group identification or irreducibility assumption enters this calculation.
Sources and raw matrix files are recorded in `Degree220Pair/source/README.md`.
Only kernel-checked reduction is used for the numerical certificates.
-/

open Thompson.BinaryMatrix
@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair

private def traceProduct (n : ℕ) (a b : Array ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => traceProduct n a b k ^^^ (rowProduct a[k]! b n >>> k)

private theorem bit_traceProduct (n : ℕ) (a b : Array ℕ) (k : ℕ) :
    bit (traceProduct n a b k) 0 =
      ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range n, bit a[i]! j * bit b[j]! i := by
  induction k with
  | zero => simp [traceProduct, bit]
  | succ k ih =>
    rw [traceProduct, bit_xor, ih, Finset.sum_range_succ]
    congr 1
    have hs (x : ℕ) : bit (x >>> k) 0 = bit x k := by
      simp [bit]
    rw [hs, bit_rowProduct]

private theorem trace_decode_mul (n : ℕ) (a b : Array ℕ) :
    Matrix.trace (decode n a * decode n b) = bit (traceProduct n a b n) 0 := by
  rw [bit_traceProduct, Matrix.trace]
  change (∑ i : Fin n, ∑ j : Fin n, bit a[i.val]! j.val * bit b[j.val]! i.val) = _
  calc
    _ = ∑ i : Fin n, ∑ j ∈ Finset.range n, bit a[i.val]! j * bit b[j]! i.val := by
      apply Finset.sum_congr rfl
      intro i _
      exact Fin.sum_univ_eq_sum_range (fun j => bit a[i.val]! j * bit b[j]! i.val) n
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun i => ∑ j ∈ Finset.range n, bit a[i]! j * bit b[j]! i) n

/-- The first pair has trace one at the product of its two generators. -/
theorem trace_first : Matrix.trace (matrixA false * matrixB false) = 1 := by
  rw [matrixA, matrixB]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm,
    trace_decode_mul]
  decide +kernel

/-- The second pair has trace zero at the same generator word. -/
theorem trace_second : Matrix.trace (matrixA true * matrixB true) = 0 := by
  rw [matrixA, matrixB]
  simp only [↓reduceIte]
  rw [← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm,
    trace_decode_mul]
  decide +kernel

/-- Binary traces distinguish the two literal matrix pairs. -/
theorem traces_ne : Matrix.trace (matrixA false * matrixB false) ≠
    Matrix.trace (matrixA true * matrixB true) := by
  rw [trace_first, trace_second]
  exact one_ne_zero

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair
