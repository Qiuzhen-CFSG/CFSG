module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Packed
import Mathlib.Data.List.GetD
/-!
# Balanced, checked products of packed GF(4) rows

A tree stores a matrix's rows in their original order. Each branch records its
left subtree's length; `valid` checks that annotation. Products recursively
combine the two intervals by XOR. Their equality with the existing list-based
product is proved by concatenation, so no numerical operation is trusted.
`eval_product` and `eval_inverse` turn kernel-checked Boolean certificates into
identities of the actual matrices over `Four`.

This avoids repeatedly unfolding a long list during kernel reduction. The
application is to HSG1-f4r896aB0; exact source attribution is retained in
`TracePair/source/README.md`, and measurements are in this directory's source
README. All numerical certificates still require kernel checking.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Balanced
open Certificates
open Packed

inductive Tree where
  | empty
  | leaf (row : Row)
  | node (leftSize : ℕ) (left right : Tree)
  deriving DecidableEq

def rows : Tree → Mat
  | .empty => []
  | .leaf r => [r]
  | .node _ l r => rows l ++ rows r

def valid : Tree → Bool
  | .empty => true
  | .leaf _ => true
  | .node n l r => (rows l).length == n && valid l && valid r

/-- Compose bounded interval certificates without flattening a whole matrix again. -/
theorem node_spec (m n : ℕ) (l r : Tree)
    (hl : (rows l).length = m ∧ valid l = true)
    (hr : (rows r).length = n ∧ valid r = true) :
    (rows (.node m l r)).length = m + n ∧ valid (.node m l r) = true := by
  simp only [rows, List.length_append, valid, hl.1, hr.1, hl.2, hr.2, beq_self_eq_true,
    Bool.true_and, and_self]

def selected (a b : Row) (k : ℕ) : Row :=
  Base.addRow (if a.1.testBit k then b else (0, 0))
    (if a.2.testBit k then Base.timesT b else (0, 0))

def product (a : Row) : Tree → ℕ → Row
  | .empty, _ => (0, 0)
  | .leaf b, k => selected a b k
  | .node n l r, k => Base.addRow (product a l k) (product a r (k + n))

private theorem addRow_assoc (a b c : Row) :
    Base.addRow (Base.addRow a b) c = Base.addRow a (Base.addRow b c) := by
  exact Prod.ext (Nat.xor_assoc ..) (Nat.xor_assoc ..)

private theorem rowProductFrom_append (a : Row) (l r : Mat) (k : ℕ) :
    rowProductFrom a (l ++ r) k =
      Base.addRow (rowProductFrom a l k) (rowProductFrom a r (k + l.length)) := by
  induction l generalizing k with
  | nil => simp [rowProductFrom, Base.addRow]
  | cons b bs ih =>
    simp only [List.cons_append, List.length_cons, rowProductFrom, ih, addRow_assoc]
    rw [Nat.add_assoc, Nat.add_comm 1 bs.length]

theorem product_eq (a : Row) (t : Tree) (h : valid t = true) (k : ℕ) :
    product a t k = rowProductFrom a (rows t) k := by
  induction t generalizing k with
  | empty => rfl
  | leaf b => simp [product, rows, rowProductFrom, selected, Base.addRow]
  | node n l r il ir =>
    simp only [valid, Bool.and_eq_true, beq_iff_eq] at h
    rw [product, il h.1.2, ir h.2, rows, rowProductFrom_append, h.1.1]

def allFrom (p : ℕ → Row → Bool) : Tree → ℕ → Bool
  | .empty, _ => true
  | .leaf a, k => p k a
  | .node n l r, k => allFrom p l k && allFrom p r (k + n)

theorem of_allFrom (p : ℕ → Row → Bool) (t : Tree) (hv : valid t = true)
    (k : ℕ) (h : allFrom p t k = true) (i : ℕ) (hi : i < (rows t).length) :
    p (k + i) ((rows t).getD i (0, 0)) = true := by
  induction t generalizing k i with
  | empty => simp [rows] at hi
  | leaf a =>
    have : i = 0 := by simpa [rows] using hi
    subst i
    simpa [rows, allFrom] using h
  | node n l r il ir =>
    simp only [valid, Bool.and_eq_true, beq_iff_eq] at hv
    simp only [allFrom, Bool.and_eq_true] at h
    change p (k + i) (((rows l) ++ (rows r)).getD i (0, 0)) = true
    by_cases hil : i < (rows l).length
    · rw [List.getD_append _ _ _ _ hil]
      exact il hv.1.2 k h.1 i hil
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      have hir : i - (rows l).length < (rows r).length := by
        simp only [rows, List.length_append] at hi
        omega
      have hh := ir hv.2 (k + n) h.2 (i - (rows l).length) hir
      have hn := hv.1.1
      have hk : k + n + (i - (rows l).length) = k + i := by omega
      simpa only [hk] using hh

def checkProduct (a b : Tree) (c : Mat) : Bool :=
  allFrom (fun i r => product r b 0 == c.getD i (0, 0)) a 0

def checkInverse (a b : Tree) : Bool :=
  allFrom (fun i r => product r b 0 == (2 ^ i, 0)) a 0

theorem eval_product (n : ℕ) (a b : Tree) (c : Mat)
    (ha : (rows a).length = n) (hb : (rows b).length = n)
    (hva : valid a = true) (hvb : valid b = true) (h : checkProduct a b c = true) :
    Packed.eval n (rows a) * Packed.eval n (rows b) = Packed.eval n c := by
  apply Packed.eval_product n _ _ _ hb
  intro i
  have hh := of_allFrom _ a hva 0 h i.val (by simp [ha])
  simp only [Nat.zero_add, beq_iff_eq] at hh
  rw [product_eq _ _ hvb] at hh
  exact hh

theorem eval_inverse (n : ℕ) (a b : Tree)
    (ha : (rows a).length = n) (hb : (rows b).length = n)
    (hva : valid a = true) (hvb : valid b = true) (h : checkInverse a b = true) :
    Packed.eval n (rows a) * Packed.eval n (rows b) = 1 := by
  apply Packed.eval_inverse n _ _ hb
  intro i
  have hh := of_allFrom _ a hva 0 h i.val (by simp [ha])
  simp only [Nat.zero_add, beq_iff_eq] at hh
  rw [product_eq _ _ hvb] at hh
  exact hh
end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Balanced
