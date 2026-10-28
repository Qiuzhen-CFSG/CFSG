module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.RowChecker
/-!
# Bounded row certificates for binary matrix multiplication

Boolean checking on consecutive row intervals is sound for the existing
list-product decoder. Combining short certificates keeps each kernel reduction
small; it does not change the ordinary matrix multiplication being proved.
The max3 product modules are the concrete consumers of this checker.
-/

@[expose] public section
namespace Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates

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

theorem checked_mul (n : ℕ) (a b c : Array ℕ) (hb : b.size = n)
    (h : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == c[i]!) 0 n = true) :
    BinaryMatrix.decode n a * BinaryMatrix.decode n b = BinaryMatrix.decode n c := by
  apply BinaryMatrix.decode_mul_list n a b c hb
  intro i
  simpa only [Nat.zero_add, beq_iff_eq] using ((checkRange_spec _ _ _).mp h i.val i.isLt)

theorem checked_mul_one (n : ℕ) (a b : Array ℕ) (hb : b.size = n)
    (h : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == 2 ^ i) 0 n = true) :
    BinaryMatrix.decode n a * BinaryMatrix.decode n b = 1 := by
  apply BinaryMatrix.decode_mul_one_list n a b hb
  intro i
  simpa only [Nat.zero_add, beq_iff_eq] using ((checkRange_spec _ _ _).mp h i.val i.isLt)

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
