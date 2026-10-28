module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

/-!
# Sequential block certificates for the large binary HS matrices

Packed rows use the bit convention of the ATLAS HS tables in
`Binary/source/README.md`. Sequential traversal avoids repeatedly indexing a
large array inside kernel reduction. `combine_append` splits any row product
into bounded blocks; `vector_combine` and `matrix_product` connect those checked
XOR identities to ordinary rectangular matrices over `ZMod 2`.

The bit-level interpretation is inherited from the Thompson certificate checker.
No computation outside Lean is trusted by these soundness lemmas.
-/

@[expose] public section

open scoped BigOperators
open Thompson.BinaryMatrix
namespace Representation.HigmanSims.LargeModels.Binary.Large.RowArithmetic

def combine : List ℕ → ℕ → ℕ
  | [], _ => 0
  | r :: rs, x => (if x.testBit 0 then r else 0) ^^^ combine rs (x >>> 1)

theorem bit_combine (rows : List ℕ) (mask j : ℕ) :
    bit (combine rows mask) j =
      ∑ i : Fin rows.length, bit mask i.val * bit rows[i.val] j := by
  induction rows generalizing mask with
  | nil => simp [combine, bit]
  | cons r rs ih =>
    simp only [List.length_cons]
    rw [combine, bit_xor, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]
    congr 1
    · cases h : mask.testBit 0 <;> simp [bit, h]
    · apply Finset.sum_congr rfl
      intro i _
      simp only [bit, Nat.testBit_shiftRight, Nat.add_comm 1]

theorem combine_append (xs ys : List ℕ) (mask : ℕ) :
    combine (xs ++ ys) mask =
      combine xs mask ^^^ combine ys (mask >>> xs.length) := by
  induction xs generalizing mask with
  | nil => simp [combine]
  | cons r rs ih =>
    simp only [List.cons_append, combine, List.length_cons, ih, Nat.xor_assoc,
      ← Nat.shiftRight_add, Nat.add_comm 1]

def vector (n : ℕ) (x : ℕ) : Fin n → ZMod 2 := fun j => bit x j.val

def matrix (m n : ℕ) (xs : List ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit xs[i.val]! j.val

theorem vector_combine (rows : List ℕ) (n p : ℕ) (hlen : rows.length = n)
    (mask : ℕ) :
    vector p (combine rows mask) = Matrix.vecMul (vector n mask) (matrix n p rows) := by
  subst n
  funext j
  rw [vector, bit_combine]
  apply Finset.sum_congr rfl
  intro i _
  simp only [matrix, vector, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem i.isLt, Option.getD_some]

theorem matrix_product (m n p : ℕ) (xs ys zs : List ℕ) (hy : ys.length = n)
    (h : ∀ i : Fin m, combine ys xs[i.val]! = zs[i.val]!) :
    matrix m n xs * matrix n p ys = matrix m p zs := by
  funext i
  exact (vector_combine ys n p hy xs[i.val]!).symm.trans (congrArg (vector p) (h i))

theorem matrix_toList (n : ℕ) (xs : Array ℕ) :
    matrix n n xs.toList = Thompson.BinaryMatrix.decode n xs := by
  funext i j
  simp only [matrix, Thompson.BinaryMatrix.decode, Array.getElem!_toList]

/-- Assemble two independently checked blocks without re-evaluating their rows. -/
theorem combine_append_checked (xs ys : List ℕ) (mask next left right out : ℕ)
    (hx : combine xs mask = left) (hshift : mask >>> xs.length = next)
    (hy : combine ys next = right) (hout : left ^^^ right = out) :
    combine (xs ++ ys) mask = out := by
  rw [combine_append, hx, hshift, hy, hout]

/-- A checked row of a square product, stated using the shared array decoder. -/
theorem decode_product_row (n : ℕ) (xs ys : Array ℕ) (i : Fin n) (out : ℕ)
    (hlen : ys.size = n) (h : combine ys.toList xs[i.val]! = out) :
    (Thompson.BinaryMatrix.decode n xs * Thompson.BinaryMatrix.decode n ys) i =
      vector n out := by
  have hr := vector_combine ys.toList n n (by simpa using hlen) xs[i.val]!
  rw [matrix_toList] at hr
  exact hr.symm.trans (congrArg (vector n) h)

/-- The particularly useful identity-matrix row conclusion. -/
theorem decode_product_one_row (n : ℕ) (xs ys : Array ℕ) (i : Fin n)
    (hlen : ys.size = n) (h : combine ys.toList xs[i.val]! = 2 ^ i.val) :
    (Thompson.BinaryMatrix.decode n xs * Thompson.BinaryMatrix.decode n ys) i =
      (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i := by
  rw [decode_product_row n xs ys i _ hlen h]
  funext j
  simp [vector, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

end Representation.HigmanSims.LargeModels.Binary.Large.RowArithmetic
