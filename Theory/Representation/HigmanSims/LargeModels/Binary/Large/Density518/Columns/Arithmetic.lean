module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Blocks
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Orbit
/-!
# Soundness of bounded column certificates

Sequential bit extraction certifies each transpose against the literal ATLAS
matrix; packed row multiplication then gives its left action on columns.
Range concatenation assembles bounded checks without a large finite reduction.
The column bit proof adapts this repository's `Restricted1408` column checker.
Source: R. A. Wilson et al., ATLAS HSG1-f2r518B0; see `source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density518.Columns
open RowArithmetic

def InRange (p : ℕ → Prop) (start count : ℕ) : Prop :=
  ∀ i : Fin count, p (start + i.val)

theorem InRange.join {p : ℕ → Prop} (start m n : ℕ)
    (h : InRange p start m) (k : InRange p (start + m) n) :
    InRange p start (m + n) := by
  intro i
  by_cases hi : i.val < m
  · exact h ⟨i.val, hi⟩
  · have hin : i.val - m < n := by omega
    have hk := k ⟨i.val - m, hin⟩
    have he : start + m + (i.val - m) = start + i.val := by omega
    simpa only [he] using hk

theorem InRange.all {p : ℕ → Prop} {n : ℕ} (h : InRange p 0 n) :
    ∀ i : Fin n, p i.val := by
  simpa only [InRange, Nat.zero_add] using h

def column (j : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs => 2 * column j rs + if r.testBit j then 1 else 0

theorem column_bit (j : ℕ) (rs : List ℕ) (i : ℕ) :
    (column j rs).testBit i = rs[i]!.testBit j := by
  induction rs generalizing i with
  | nil => simp [column]
  | cons r rs ih =>
    have hb : (if r.testBit j then 1 else 0) < 2^1 := by split <;> decide
    rw [column, show 2 = 2^1 from rfl, Nat.testBit_two_pow_mul_add _ hb]
    cases i with
    | zero => cases h : r.testBit j <;> simp [h]
    | succ i => simpa [List.getElem!_cons_succ] using ih i

theorem column_append (j : ℕ) (xs ys : List ℕ) :
    column j (xs ++ ys) = 2 ^ xs.length * column j ys + column j xs := by
  induction xs with
  | nil => simp [column]
  | cons r rs ih =>
    simp only [List.cons_append, column, List.length_cons, ih, pow_succ]
    ring

theorem column_append_checked (xs ys : List ℕ) (j left right out : ℕ)
    (hx : column j xs = left) (hy : column j ys = right)
    (hout : 2 ^ xs.length * right + left = out) :
    column j (xs ++ ys) = out := by
  rw [column_append, hx, hy, hout]

theorem transpose_of_columns {n : ℕ} (a t : Array ℕ)
    (h : ∀ j : Fin n, column j.val a.toList = t[j.val]!) :
    Thompson.BinaryMatrix.decode n t = (Thompson.BinaryMatrix.decode n a).transpose := by
  funext j i
  change Thompson.BinaryMatrix.bit t[j.val]! i.val =
    Thompson.BinaryMatrix.bit a[i.val]! j.val
  simp only [Thompson.BinaryMatrix.bit, ← h j, column_bit, Array.getElem!_toList]

theorem vector_mul_checked (a : Array ℕ) (x y : ℕ)
    (hlen : a.size = 518) (h : combine a.toList x = y) :
    Matrix.vecMul (vector 518 x) (Thompson.BinaryMatrix.decode 518 a) = vector 518 y := by
  have hh := vector_combine a.toList 518 518 (by simpa using hlen) x
  rw [matrix_toList, h] at hh
  exact hh.symm

end Representation.HigmanSims.LargeModels.Binary.Large.Density518.Columns
