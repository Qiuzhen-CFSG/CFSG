module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.RowArithmetic
import Mathlib.Data.List.GetD
/-!
# Balanced packed rows for the degree-1000 exterior section

A node records its left interval length and its power of two. Validity checks
both annotations. Splitting a mask by division and remainder then computes
exactly `RowArithmetic.combine`; lookup has the same literal row order as the
flattened list. These interfaces keep the large numerical certificates under
narrow imports. They contain no external-computation assumption.

Application and source: ATLAS HSG1-f2r56B0/HSG1-f2r1000B0 and
`Binary/source/section1000.json`; see `Binary/source/README.md` for attribution
and rights. Original repository code under Apache 2.0.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining
open RowArithmetic

inductive RowTree where
  | leaf (row : ℕ)
  | node (n divisor : ℕ) (left right : RowTree)

def RowTree.rows : RowTree → List ℕ
  | .leaf r => [r]
  | .node _ _ l r => l.rows ++ r.rows

def RowTree.Valid : RowTree → Prop
  | .leaf _ => True
  | .node n d l r => l.rows.length = n ∧ d = 2^n ∧ l.Valid ∧ r.Valid

instance decidableValid : (t : RowTree) → Decidable t.Valid
  | .leaf _ => isTrue trivial
  | .node n d l r =>
    letI := decidableValid l
    letI := decidableValid r
    inferInstanceAs (Decidable (l.rows.length = n ∧ d = 2^n ∧ l.Valid ∧ r.Valid))

def RowTree.product : RowTree → ℕ → ℕ
  | .leaf r, x => if x % 2 = 1 then r else 0
  | .node _ d l r, x => Nat.xor (l.product (x % d)) (r.product (x / d))

def RowTree.get : RowTree → ℕ → ℕ
  | .leaf r, i => if i = 0 then r else 0
  | .node n _ l r, i => if i < n then l.get i else r.get (i - n)

theorem combine_mod (xs : List ℕ) (x : ℕ) :
    combine xs (x % 2^xs.length) = combine xs x := by
  induction xs generalizing x with
  | nil => rfl
  | cons r rs ih =>
    simp only [combine, Nat.testBit_mod_two_pow, List.length_cons,
      Nat.zero_lt_succ, decide_true, Bool.true_and]
    congr 1
    rw [← ih (x >>> 1)]
    congr 1
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
    simp only [Nat.add_comm 1 i, Nat.add_lt_add_iff_right]

theorem RowTree.product_eq (t : RowTree) (h : t.Valid) (x : ℕ) :
    t.product x = combine t.rows x := by
  induction t generalizing x with
  | leaf r =>
    simp only [product, rows, combine, Nat.xor_zero]
    simp only [Nat.testBit_zero, decide_eq_true_eq]
  | node n d l r il ir =>
    obtain ⟨hn, hd, hl, hr⟩ := h
    simp only [product, rows, combine_append, il hl, ir hr]
    rw [hd, ← hn, combine_mod, Nat.shiftRight_eq_div_pow]
    rfl

theorem RowTree.get_eq (t : RowTree) (h : t.Valid) (i : ℕ) :
    t.get i = t.rows[i]! := by
  induction t generalizing i with
  | leaf r =>
    cases i <;> simp [get, rows]
  | node n d l r il ir =>
    obtain ⟨hn, _, hl, hr⟩ := h
    simp only [get, rows, List.getElem!_eq_getElem?_getD]
    change (if i < n then l.get i else r.get (i-n)) = (l.rows ++ r.rows).getD i 0
    split
    · rw [List.getD_append _ _ _ _ (by omega), il hl]
      simp only [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rfl
    · rw [List.getD_append_right _ _ _ _ (by omega), ir hr, hn]
      simp only [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rfl


theorem RowTree.node_valid (n m d : ℕ) (l r : RowTree)
    (hl : l.rows.length = n ∧ l.Valid) (hr : r.rows.length = m ∧ r.Valid)
    (hd : d = 2^n) :
    (RowTree.node n d l r).rows.length = n + m ∧ (RowTree.node n d l r).Valid := by
  exact ⟨by simp only [rows, List.length_append, hl.1, hr.1],
    hl.1, hd, hl.2, hr.2⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining
