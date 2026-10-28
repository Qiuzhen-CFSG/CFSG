module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Arithmetic

/-!
# Bounded packed multiplication for the literal algebra words

This evaluator uses the existing `RowArithmetic.combine` in leaves. Each
node carries a kernel-checked literal power of two, and zero blocks are
skipped. `product_eq` proves exact agreement with the shared row arithmetic;
`tree_matrix_product` turns checked row batches into ordinary matrix products.
The six concrete products and three sums feed `RankOne.decoded_algebra_eq`.

Source: R. A. Wilson et al., ATLAS HSG1-f2r1000B0; attribution and rights in
`Binary/source/README.md`. New code is Apache-2.0.
-/

@[expose] public section
open Matrix Thompson.BinaryMatrix
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra
open RowArithmetic

theorem combine_zero (rs : List ℕ) : combine rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [combine, ih]

theorem combine_mod (rs : List ℕ) (x : ℕ) : combine rs (x % 2^rs.length) = combine rs x := by
  induction rs generalizing x with
  | nil => rfl
  | cons r rs ih =>
    simp only [combine, List.length_cons, Nat.testBit_mod_two_pow]
    simp only [Nat.zero_lt_succ, decide_true, Bool.true_and]
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    simp only [Nat.pow_one]
    rw [pow_succ', Nat.mod_mul_right_div_self, ih]

inductive ProductTree where
  | leaf (rows : List ℕ)
  | node (divisor : ℕ) (left right : ProductTree)

def ProductTree.rows : ProductTree → List ℕ
  | .leaf rs => rs
  | .node _ l r => l.rows ++ r.rows

def ProductTree.valid : ProductTree → Bool
  | .leaf _ => true
  | .node d l r => decide (d = 2^l.rows.length) && l.valid && r.valid

def ProductTree.product (x : ℕ) (t : ProductTree) : ℕ :=
  if x = 0 then 0 else match t with
  | .leaf rs => combine rs x
  | .node d l r => l.product (x % d) ^^^ r.product (x / d)

theorem ProductTree.product_eq (t : ProductTree) (ht : t.valid = true) (x : ℕ) :
    t.product x = combine t.rows x := by
  induction t generalizing x with
  | leaf rs =>
    by_cases hx : x = 0
    · simp [ProductTree.product, ProductTree.rows, hx, combine_zero]
    · simp [ProductTree.product, ProductTree.rows, hx]
  | node d l r ihl ihr =>
    simp only [ProductTree.valid, Bool.and_eq_true, decide_eq_true_eq] at ht
    by_cases hx : x = 0
    · simp [ProductTree.product, ProductTree.rows, hx, combine_zero]
    · simp only [ProductTree.product, hx, ↓reduceIte, ProductTree.rows, combine_append]
      rw [ihl ht.1.2, ihr ht.2, ht.1.1, combine_mod, Nat.shiftRight_eq_div_pow]

theorem map_append_checked (f : ℕ → ℕ) {a b c d : List ℕ}
    (ha : a.map f = c) (hb : b.map f = d) : (a ++ b).map f = c ++ d := by
  rw [List.map_append, ha, hb]

theorem tree_matrix_product (t : ProductTree) (ht : t.valid = true)
    (n : ℕ) (xs ys : List ℕ) (hlen : t.rows.length = n)
    (hx : xs.length = n) (h : xs.map t.product = ys) :
    matrix n n xs * matrix n n t.rows = matrix n n ys := by
  apply matrix_product n n n xs t.rows ys hlen
  intro i
  have hi : i.val < xs.length := by omega
  subst ys
  simpa only [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
    using (t.product_eq ht xs[i.val]).symm

def xorRows : List ℕ → List ℕ → List ℕ
  | x :: xs, y :: ys => (x ^^^ y) :: xorRows xs ys
  | _, _ => []

theorem xorRows_get (xs ys : List ℕ) (h : xs.length = ys.length)
    (i : ℕ) (hi : i < xs.length) : (xorRows xs ys)[i]! = xs[i]! ^^^ ys[i]! := by
  induction xs generalizing ys i with
  | nil => simp at hi
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i =>
        simpa [xorRows] using ih ys (by simpa using h) i (Nat.lt_of_succ_lt_succ hi)

theorem matrix_xorRows (n : ℕ) (xs ys : List ℕ)
    (hx : xs.length = n) (hy : ys.length = n) :
    matrix n n (xorRows xs ys) = matrix n n xs + matrix n n ys := by
  funext i j
  change bit (xorRows xs ys)[i.val]! j.val = bit xs[i.val]! j.val + bit ys[i.val]! j.val
  rw [xorRows_get xs ys (hx.trans hy.symm) i.val (by omega), bit_xor]

theorem xorRows_append (a b c d : List ℕ) (hlen : a.length = c.length) :
    xorRows (a ++ b) (c ++ d) = xorRows a c ++ xorRows b d := by
  induction a generalizing c with
  | nil =>
    have hc : c = [] := List.length_eq_zero_iff.mp hlen.symm
    subst c
    rfl
  | cons x a ih =>
    cases c with
    | nil => simp at hlen
    | cons y c =>
      simpa only [List.cons_append, xorRows] using
        congrArg (List.cons (x ^^^ y)) (ih c (by simpa using hlen))

theorem xor_append_checked {a b c d e f : List ℕ} (hlen : a.length = c.length)
    (ha : xorRows a c = e) (hb : xorRows b d = f) :
    xorRows (a ++ b) (c ++ d) = e ++ f := by
  rw [xorRows_append a b c d hlen, ha, hb]

theorem matrix_identity_rows (n : ℕ) :
    matrix n n (List.ofFn (fun i : Fin n => 2^i.val)) = 1 := by
  funext i j
  simp [matrix, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra
