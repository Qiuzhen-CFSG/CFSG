module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.Arithmetic

/-!
# Bounded row checks for the binary degree-320 certificates

Skipping XOR at zero mask bits preserves the original packed multiplication.
The append and split lemmas let independently kernel-checked small row blocks
prove a full product, without one large reduction retaining all intermediate
rows. The concrete consumer is the native trace reduction in `TraceReduction.lean`.
The original numerical data are attributed in `../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates

def skipRow (a : ℕ) : List ℕ → ℕ
  | [] => 0
  | b :: bs => if a % 2 = 1 then b ^^^ skipRow (a / 2) bs else skipRow (a / 2) bs

def checkSkip : List ℕ → List ℕ → List ℕ → Bool
  | [], _, [] => true
  | a :: as, b, c :: cs => (skipRow a b == c) && checkSkip as b cs
  | _, _, _ => false

theorem skipRow_eq (a : Nat) (b : List Nat) : skipRow a b = shiftRow a b := by
  induction b generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [skipRow, shiftRow, ih, Nat.testBit_eq_decide_div_mod_eq,
      pow_zero, Nat.div_one, decide_eq_true_eq]
    split <;> simp_all

theorem checkSkip_eq (a b c : List Nat) : checkSkip a b c = checkRows a b c := by
  induction a generalizing c with
  | nil => cases c <;> rfl
  | cons x xs ih => cases c <;> simp [checkSkip, checkRows, skipRow_eq, ih]

theorem checkRows_append (a₁ a₂ b c₁ c₂ : List Nat)
    (h₁ : checkRows a₁ b c₁ = true) (h₂ : checkRows a₂ b c₂ = true) :
    checkRows (a₁ ++ a₂) b (c₁ ++ c₂) = true := by
  induction a₁ generalizing c₁ with
  | nil => cases c₁ <;> simp_all [checkRows]
  | cons x xs ih =>
    cases c₁ with
    | nil => simp [checkRows] at h₁
    | cons y ys =>
      simp only [checkRows, Bool.and_eq_true] at h₁
      simp only [List.cons_append, checkRows, Bool.and_eq_true]
      exact ⟨h₁.1, ih _ h₁.2⟩

theorem checkRows_split (a b c : List Nat) (k : Nat)
    (h₁ : checkRows (a.take k) b (c.take k) = true)
    (h₂ : checkRows (a.drop k) b (c.drop k) = true) : checkRows a b c = true := by
  simpa only [List.take_append_drop] using
    checkRows_append (a.take k) (a.drop k) b (c.take k) (c.drop k) h₁ h₂

/-- A small block can be checked using the implementation that avoids XOR
at every zero mask bit. Its conclusion is the original public checker. -/
theorem checkRows_of_skip (a b c : List Nat) (h : checkSkip a b c = true) :
    checkRows a b c = true := by
  simpa only [checkSkip_eq] using h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates
