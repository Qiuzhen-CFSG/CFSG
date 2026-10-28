module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Bits

/-!
# Rectangular packed binary matrix checks

A row mask selects and XORs rows of the right factor. The bit calculation
reuses `Thompson.BinaryMatrix.bit_xor`; list traversal follows the M22
Hermitian-filtration checker. We prove rectangular multiplication and packed
transpose soundness, then extract checked rows in bounded batches.

The consumers certify the quotient of the native fifth exterior power and
its dual comparison, using the witnesses described in `../source/README.md`.
Source context: James, J. Algebra 27 (1973), 57--111; GM02 Proposition 5.1.
-/

@[expose] public section
open Thompson.BinaryMatrix
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.CertificatePacked

def combine : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, mask => (if mask.testBit 0 then x else 0) ^^^ combine xs (mask / 2)

@[simp] theorem combine_zero (xs : List ℕ) : combine xs 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [combine, ih]

theorem bit_combine (n : ℕ) (c : Fin n → ℕ) (v r : ℕ) :
    bit (combine (List.ofFn c) v) r = ∑ j, bit (c j) r * bit v j.val := by
  induction n generalizing v with
  | zero => simp [List.ofFn_zero, combine, bit]
  | succ n ih =>
    rw [List.ofFn_succ, combine, bit_xor, ih, Fin.sum_univ_succ]
    congr 1
    · cases h : v.testBit 0 <;> simp [bit, h]
    · apply Finset.sum_congr rfl
      intro j _
      simp only [bit, Nat.testBit_div_two, Fin.val_succ]

def matrix (m n : ℕ) (xs : List ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit xs[i.val]! j.val

theorem matrix_mul_entry {m n p : ℕ} (xs ys : List ℕ) (hy : ys.length = n)
    (i : Fin m) (j : Fin p) :
    (matrix m n xs * matrix n p ys) i j = bit (combine ys xs[i.val]!) j.val := by
  have he : List.ofFn (fun k : Fin n => ys[k.val]!) = ys := by subst n; simp
  rw [← he, bit_combine]
  simp [matrix, Matrix.mul_apply, mul_comm]

def checkProduct (ys : List ℕ) : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, z :: zs => combine ys x == z && checkProduct ys xs zs
  | _, _ => false

theorem checkProduct_sound (ys xs zs : List ℕ) (h : checkProduct ys xs zs = true)
    (i : ℕ) : combine ys xs[i]! = zs[i]! := by
  induction xs generalizing zs i with
  | nil => cases zs <;> simp_all [checkProduct]
  | cons x xs ih =>
    cases zs with
    | nil => simp [checkProduct] at h
    | cons z zs =>
      simp only [checkProduct, Bool.and_eq_true, beq_iff_eq] at h
      cases i with
      | zero => exact h.1
      | succ i => exact ih zs h.2 i

theorem matrix_product {m n p : ℕ} (xs ys zs : List ℕ) (hy : ys.length = n)
    (h : checkProduct ys xs zs = true) : matrix m n xs * matrix n p ys = matrix m p zs := by
  ext i j
  rw [matrix_mul_entry xs ys hy, checkProduct_sound ys xs zs h i.val]
  rfl

def checkEqualProducts (ys ws : List ℕ) : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, z :: zs => combine ys x == combine ws z && checkEqualProducts ys ws xs zs
  | _, _ => false

theorem checkEqualProducts_sound (ys ws xs zs : List ℕ)
    (h : checkEqualProducts ys ws xs zs = true) (i : ℕ) :
    combine ys xs[i]! = combine ws zs[i]! := by
  induction xs generalizing zs i with
  | nil => cases zs <;> simp_all [checkEqualProducts]
  | cons x xs ih =>
    cases zs with
    | nil => simp [checkEqualProducts] at h
    | cons z zs =>
      simp only [checkEqualProducts, Bool.and_eq_true, beq_iff_eq] at h
      cases i with
      | zero => exact h.1
      | succ i => exact ih zs h.2 i

theorem matrix_equal_products {m n p q : ℕ} (xs ys zs ws : List ℕ)
    (hy : ys.length = n) (hw : ws.length = q)
    (h : checkEqualProducts ys ws xs zs = true) :
    matrix m n xs * matrix n p ys = matrix m q zs * matrix q p ws := by
  ext i j
  rw [matrix_mul_entry xs ys hy, matrix_mul_entry zs ws hw,
    checkEqualProducts_sound ys ws xs zs h i.val]

def checkIdentity (ys : List ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | x :: xs, i => combine ys x == 2 ^ i && checkIdentity ys xs (i+1)

theorem checkIdentity_sound (ys xs : List ℕ) (start : ℕ)
    (h : checkIdentity ys xs start = true) (i : ℕ) (hi : i < xs.length) :
    combine ys xs[i]! = 2 ^ (start+i) := by
  induction xs generalizing start i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [checkIdentity, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i => simpa [Nat.add_assoc, Nat.add_comm 1] using ih (start+1) h.2 i (by simpa using hi)

theorem matrix_identity {m n : ℕ} (xs ys : List ℕ) (hx : xs.length = m)
    (hy : ys.length = n) (h : checkIdentity ys xs 0 = true) :
    matrix m n xs * matrix n m ys = 1 := by
  ext i j
  rw [matrix_mul_entry xs ys hy, checkIdentity_sound ys xs 0 h i.val (hx ▸ i.isLt)]
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

-- Recursively collect one column; all arithmetic is checked by the kernel.
def column (xs : List ℕ) (j : ℕ) : ℕ :=
  match xs with
  | [] => 0
  | x :: xs => Nat.bit (x.testBit j) (column xs j)

theorem testBit_column (xs : List ℕ) (i j : ℕ) (hi : i < xs.length) :
    (column xs j).testBit i = xs[i]!.testBit j := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [column]
    | succ i => simpa [column, Nat.testBit_bit_succ] using ih i (by simpa using hi)

def checkTranspose (xs : List ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | y :: ys, j => column xs j == y && checkTranspose xs ys (j+1)

theorem checkTranspose_sound (xs ys : List ℕ) (start : ℕ)
    (h : checkTranspose xs ys start = true) (j : ℕ) (hj : j < ys.length) :
    column xs (start+j) = ys[j]! := by
  induction ys generalizing start j with
  | nil => simp at hj
  | cons y ys ih =>
    simp only [checkTranspose, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero => simpa using h.1
    | succ j => simpa [Nat.add_assoc, Nat.add_comm 1] using ih (start+1) h.2 j (by simpa using hj)

theorem matrix_transpose {m n : ℕ} (xs ys : List ℕ) (hx : xs.length = m)
    (hy : ys.length = n) (h : checkTranspose xs ys 0 = true) :
    (matrix m n xs).transpose = matrix n m ys := by
  ext i j
  have he := checkTranspose_sound xs ys 0 h i.val (hy ▸ i.isLt)
  simp only [Nat.zero_add] at he
  change bit xs[j.val]! i.val = bit ys[i.val]! j.val
  rw [← he]
  unfold bit
  rw [testBit_column xs j.val i.val (hx ▸ j.isLt)]

theorem checkIdentity_append (ys xs zs : List ℕ) (start : ℕ) :
    checkIdentity ys (xs ++ zs) start =
      (checkIdentity ys xs start && checkIdentity ys zs (start + xs.length)) := by
  induction xs generalizing start with
  | nil => simp [checkIdentity]
  | cons x xs ih => simp [checkIdentity, ih, Bool.and_assoc, Nat.add_assoc, Nat.add_comm 1]

theorem checkEqualProducts_append (ys ws xs zs xs' zs' : List ℕ)
    (hlen : xs.length = zs.length) :
    checkEqualProducts ys ws (xs ++ xs') (zs ++ zs') =
      (checkEqualProducts ys ws xs zs && checkEqualProducts ys ws xs' zs') := by
  induction xs generalizing zs with
  | nil => have hz : zs = [] := List.eq_nil_of_length_eq_zero hlen.symm
           subst zs
           simp [checkEqualProducts]
  | cons x xs ih =>
    cases zs with
    | nil => simp at hlen
    | cons z zs => simp_all [checkEqualProducts, Bool.and_assoc]

theorem chunk_entry (xs : List ℕ) (start size i : ℕ) (hi : i < size) :
    ((xs.drop start).take size)[i]! = xs[start+i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop, hi]

theorem chunk_length (xs : List ℕ) (start size : ℕ)
    (h : start + size ≤ xs.length) : ((xs.drop start).take size).length = size := by
  simp only [List.length_take, List.length_drop]
  omega

theorem forall_batches {blocks size : ℕ} (hs : 0 < size) (P : ℕ → Prop)
    (h : ∀ b : Fin blocks, ∀ j : Fin size, P (b.val * size + j.val)) :
    ∀ i : Fin (blocks * size), P i.val := by
  intro i
  have hb : i.val / size < blocks := (Nat.div_lt_iff_lt_mul hs).mpr i.isLt
  have hj : i.val % size < size := Nat.mod_lt _ hs
  have he : i.val / size * size + i.val % size = i.val := Nat.div_add_mod' _ _
  rw [← he]
  exact h ⟨i.val / size, hb⟩ ⟨i.val % size, hj⟩

theorem matrix_product_of_rows {m n p : ℕ} (xs ys zs : List ℕ)
    (hy : ys.length = n)
    (h : ∀ i : Fin m, combine ys xs[i.val]! = zs[i.val]!) :
    matrix m n xs * matrix n p ys = matrix m p zs := by
  ext i j
  rw [matrix_mul_entry xs ys hy, h i]
  rfl

theorem matrix_equal_products_of_rows {m n p q : ℕ} (xs ys zs ws : List ℕ)
    (hy : ys.length = n) (hw : ws.length = q)
    (h : ∀ i : Fin m, combine ys xs[i.val]! = combine ws zs[i.val]!) :
    matrix m n xs * matrix n p ys = matrix m q zs * matrix q p ws := by
  ext i j
  rw [matrix_mul_entry xs ys hy, matrix_mul_entry zs ws hw, h i]

theorem matrix_identity_of_rows {m n : ℕ} (xs ys : List ℕ) (hy : ys.length = n)
    (h : ∀ i : Fin m, combine ys xs[i.val]! = 2 ^ i.val) :
    matrix m n xs * matrix n m ys = 1 := by
  ext i j
  rw [matrix_mul_entry xs ys hy, h i]
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

theorem matrix_transpose_of_rows {m n : ℕ} (xs ys : List ℕ) (hx : xs.length = m)
    (h : ∀ i : Fin n, column xs i.val = ys[i.val]!) :
    (matrix m n xs).transpose = matrix n m ys := by
  ext i j
  change bit xs[j.val]! i.val = bit ys[i.val]! j.val
  rw [← h i]
  unfold bit
  rw [testBit_column xs j.val i.val (hx ▸ j.isLt)]

theorem matrix_array (m n : ℕ) (xs : Array ℕ) :
    matrix m n xs.toList = fun i j => bit xs[i.val]! j.val := by
  ext i j
  simp only [matrix, Array.getElem!_toList]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.CertificatePacked
