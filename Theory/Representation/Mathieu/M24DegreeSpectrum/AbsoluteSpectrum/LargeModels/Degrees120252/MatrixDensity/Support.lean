module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Certificate
/-!
# Rectangular checks for packed binary matrix products

Factoring the left matrix through a small row basis replaces a square product
by three rectangular identities. Matrix associativity proves the resulting
product. The M24 certificates below have rank at most ten after their initial
norm, so this avoids repeated large kernel reductions.

The packed transpose is a linear traversal of each column. Its decoding proof
avoids checking a large family of indexed scalar equalities.

Source context: the rank-one/orbit criterion for the ATLAS binary M24
candidates, explained in `../source/README.md`.
-/

@[expose] public section
open Matrix
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity

def rect {m n : ℕ} (xs : List ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit (entry xs i.val) j.val

theorem rect_product {m k n : ℕ} (a b c : List ℕ) (ha : a.length = m)
    (hb : b.length = k) (h : a.map (combineList b) = c) :
    rect (m := m) (n := k) a * rect (n := n) b = rect c := by
  ext i j
  have hi := product_rows a b c ha h i
  have he := congrArg (fun v => bit v j.val) hi
  rw [bit_combineList b k hb] at he
  simpa only [rect, Matrix.mul_apply, mul_comm, entry] using he

theorem product_of_factor {n r : ℕ} (a b c u v w : List ℕ)
    (hu : u.length = n) (hv : v.length = r) (hb : b.length = n)
    (hw : w.length = r)
    (ha : u.map (combineList v) = a)
    (hvw : v.map (combineList b) = w)
    (hc : u.map (combineList w) = c) :
    matrix (n := n) a * matrix b = matrix c := by
  have h1 := rect_product (n := n) u v a hu hv ha
  have h2 := rect_product (n := n) v b w hv hb hvw
  have h3 := rect_product (n := n) u w c hu hw hc
  change rect (m := n) (n := n) a * rect b = rect c
  rw [← h1, Matrix.mul_assoc, h2, h3]

def packBits : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (packBits bs)

theorem packBits_testBit (bs : List Bool) (j : ℕ) :
    (packBits bs).testBit j = bs[j]?.getD false := by
  induction bs generalizing j with
  | nil => simp [packBits]
  | cons b bs ih =>
    cases j with
    | zero => simp [packBits]
    | succ j => simpa only [packBits, Nat.testBit_bit_succ, List.getElem?_cons_succ] using ih j

def transposeRows (n : ℕ) (xs : List ℕ) : List ℕ :=
  (List.range n).map fun j => packBits (xs.map fun r => r.testBit j)

theorem matrix_transposeRows {n : ℕ} (xs : List ℕ) :
    matrix (n := n) (transposeRows n xs) = (matrix xs).transpose := by
  ext i j
  simp only [matrix, vector, bit, entry, transposeRows, Matrix.transpose_apply,
    List.getElem?_map, List.getElem?_range i.isLt, Option.map_some,
    Option.getD_some, packBits_testBit]
  have hb : (Option.map (fun r => r.testBit i.val) xs[j.val]?).getD false =
      (xs[j.val]?.getD 0).testBit i.val := by
    cases xs[j.val]? <;> simp
  rw [hb]
  rfl

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity
