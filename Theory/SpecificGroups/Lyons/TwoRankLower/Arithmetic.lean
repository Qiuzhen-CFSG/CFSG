module
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Arithmetic
public import Mathlib.Data.List.OfFn
/-!
# List traversal for the Lyons carry-free matrix checker

Successive radix-3125 digits multiply a literal list of rows. The sum equals
the existing row-product checker, whose soundness proves ordinary matrix
multiplication over F₅. Bounded intervals combine to cover the full matrix.
The concrete elementary eight is the consumer (Aschbacher–Smith A.2.12, p.36).
-/
@[expose] public section
namespace Lyons.TwoRank.MatrixCheck
open Atlas111WordCertificate

def listProduct : ℕ → List ℕ → ℕ
  | _, [] => 0
  | a, b :: bs => (a % radix) * b + listProduct (a / radix) bs

theorem listProduct_eq (a : ℕ) (bs : List ℕ) :
    listProduct a bs = ∑ i : Fin bs.length, digit a i.val * bs[i.val] := by
  induction bs generalizing a with
  | nil => simp [listProduct]
  | cons b bs ih =>
    rw [listProduct,ih]
    simp only [List.length_cons,Fin.sum_univ_succ,Fin.val_zero,
      List.getElem_cons_zero,Fin.val_succ,List.getElem_cons_succ,digit_succ]
    simp only [digit,pow_zero,Nat.div_one]

theorem listProduct_ofFn (a : ℕ) (b : Fin 111 → ℕ) :
    listProduct a (List.ofFn b) = rowProduct a b 111 := by
  rw [listProduct_eq,rowProduct_eq]
  simp only [List.getElem_ofFn]
  congr 1
  funext k
  have hk : Fin.ofNat 111 k.val = k := by ext; exact Nat.mod_eq_of_lt k.isLt
  rw [hk]
  rfl

theorem decode_mul_list (a b c : Fin 111 → ℕ)
    (ha : ∀ i, small 111 (a i) = true) (hb : ∀ i, small 111 (b i) = true)
    (h : ∀ i, digitsEq 111 (listProduct (a i) (List.ofFn b)) (c i) = true) :
    decode a * decode b = decode c := by
  apply decode_mul a b c ha hb
  simpa only [listProduct_ofFn] using h
theorem decode_mul_literal (a b c : Fin 111 → ℕ) (bs : List ℕ)
    (hl : List.ofFn b = bs)
    (ha : ∀ i, small 111 (a i) = true) (hb : ∀ i, small 111 (b i) = true)
    (h : ∀ i, digitsEq 111 (listProduct (a i) bs) (c i) = true) :
    decode a * decode b = decode c := by
  apply decode_mul_list a b c ha hb
  simpa only [hl] using h
def checkRange (f : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => checkRange f start n && f (start + n)

theorem checkRange_spec (f : ℕ → Bool) (start n : ℕ) :
    checkRange f start n = true ↔ ∀ i, i < n → f (start + i) = true := by
  induction n with
  | zero => simp [checkRange]
  | succ n ih =>
    rw [checkRange, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact h i hlt
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

theorem checkRange_add (f : ℕ → Bool) (start m n : ℕ) :
    checkRange f start (m + n) =
      (checkRange f start m && checkRange f (start + m) n) := by
  induction n with
  | zero => simp [checkRange]
  | succ n ih =>
    change (checkRange f start (m+n) && f (start+(m+n))) =
      (checkRange f start m && (checkRange f (start+m) n && f ((start+m)+n)))
    rw [ih, Bool.and_assoc, Nat.add_assoc]

theorem checkRange_append {f : ℕ → Bool} {start m n : ℕ}
    (hm : checkRange f start m = true) (hn : checkRange f (start + m) n = true) :
    checkRange f start (m + n) = true := by
  rw [checkRange_add, hm, hn]
  rfl

end Lyons.TwoRank.MatrixCheck
