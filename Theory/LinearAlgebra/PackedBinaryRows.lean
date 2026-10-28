module

public import Mathlib.Init

/-!
# Chunked XOR certificates for binary row actions

`rowRange` XORs the rows selected by a packed binary vector on an interval.
Intervals concatenate by XOR. `listProduct` scans a literal row block once,
so concrete checks avoid repeated lookup in a large matrix array. The bridge
`rowRange_eq_blockProduct` needs only the block's length and its row entries;
these facts can be checked once and reused for every input vector.

This is elementary binary linear algebra: bit j of an XOR is addition of
bit j over GF(2). The application to the ATLAS Baby Monster matrices is in
`BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.LargePrimes.Checker`.
-/

@[expose] public section

namespace PackedBinaryRows

def rowRange (x : Nat) (r : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => rowRange x r start n ^^^ (if x.testBit (start+n) then r (start+n) else 0)

/-- Concatenate two independently checked row ranges. -/
lemma rowRange_add (x : Nat) (r : Nat → Nat) (start m n : Nat) :
    rowRange x r start (m+n) = rowRange x r start m ^^^ rowRange x r (start+m) n := by
  induction n with
  | zero => simp [rowRange]
  | succ n ih =>
    change (rowRange x r start (m+n) ^^^ _) = rowRange x r start m ^^^ (rowRange x r (start+m) n ^^^ _)
    rw [ih, Nat.xor_assoc, Nat.add_assoc]
    rfl

def listProduct (x start : Nat) : List Nat → Nat
  | [] => 0
  | r :: rs => (if x.testBit start then r else 0) ^^^ listProduct x (start+1) rs

lemma rowRange_first (x : Nat) (r : Nat → Nat) (start n : Nat) :
    rowRange x r start (n+1) =
      (if x.testBit start then r start else 0) ^^^ rowRange x r (start+1) n := by
  rw [Nat.add_comm n 1, rowRange_add]
  simp only [rowRange, Nat.add_zero, Nat.zero_xor]

lemma rowRange_eq_listProduct (x : Nat) (r : Nat → Nat) (start : Nat) (rs : List Nat)
    (h : ∀ i, i < rs.length → r (start+i) = rs[i]!) :
    rowRange x r start rs.length = listProduct x start rs := by
  induction rs generalizing start with
  | nil => rfl
  | cons a rs ih =>
    rw [List.length_cons, rowRange_first, listProduct]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem!_cons_zero] at h0
    rw [h0, ih]
    intro i hi
    have hs := h (i+1) (by simpa using hi)
    simpa only [List.getElem!_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using hs

lemma rowRange_eq_blockProduct (x : Nat) (r : Nat → Nat) (start n : Nat)
    (rs : Array Nat) (hlen : rs.size = n)
    (h : ∀ i : Fin n, r (start+i.val) = rs[i.val]!) :
    rowRange x r start n = listProduct x start rs.toList := by
  rw [← hlen]
  apply rowRange_eq_listProduct
  intro i hi
  rw [Array.getElem!_toList]
  exact h ⟨i, by simpa [← hlen] using hi⟩

end PackedBinaryRows
