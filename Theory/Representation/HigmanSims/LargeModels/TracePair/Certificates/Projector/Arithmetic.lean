module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Packed

/-!
# Bounded packed checks for the HS null projector

The checker consumes successive low bits and skips zero coefficients. Its
soundness is proved against `Packed.rowProduct`, so the numerical checks use
only kernel reduction. This is the arithmetic layer of the rank-one perturbation
certificate for the literal ATLAS HSG1-f4r896aB0 matrices.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
open Packed

private theorem xor_left_comm (a b c : ℕ) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

private theorem xor_cancel (a b : ℕ) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- Scalar multiplication of a packed row by coefficient `k` of `a`. -/
def scaleRow (a : Row) (k : ℕ) (b : Row) : Row :=
  if a.1.testBit k then
    if a.2.testBit k then (b.1 ^^^ b.2, b.1) else b
  else if a.2.testBit k then Base.timesT b else (0, 0)

set_option linter.unusedSimpArgs false in
private theorem scaleRow_eq (a : Row) (k : ℕ) (b : Row) :
    scaleRow a k b = Base.addRow (if a.1.testBit k then b else (0, 0))
      (if a.2.testBit k then Base.timesT b else (0, 0)) := by
  cases h₀ : a.1.testBit k <;> cases h₁ : a.2.testBit k <;>
    simp [scaleRow, h₀, h₁, Base.addRow, Base.timesT, Nat.xor_assoc, xor_left_comm, xor_cancel]

theorem decode_add (a b : Row) (i : ℕ) :
    decode (Base.addRow a b) i = decode a i + decode b i := Base.entry_add omega a b i

theorem decode_scaleRow (a : Row) (k : ℕ) (b : Row) (i : ℕ) :
    decode (scaleRow a k b) i = decode a k * decode b i := by
  rw [scaleRow_eq, decode_add]
  cases h₀ : a.1.testBit k <;> cases h₁ : a.2.testBit k <;>
    simp only [Bool.false_eq_true, if_false, if_true,
      decode, Base.entry_zero, Base.entry_timesT omega omega_sq]
  all_goals simp [Base.entry,
    Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
    h₀, h₁, add_mul]

/-- The low-bit form of row multiplication, with an early zero return. -/
def product (a : Row) : Mat → Row
  | [] => (0, 0)
  | b :: bs =>
      if a = (0, 0) then (0, 0) else
      let rest := product (a.1 / 2, a.2 / 2) bs
      if a.1.testBit 0 then
        if a.2.testBit 0 then Base.addRow (b.1 ^^^ b.2, b.1) rest
        else Base.addRow b rest
      else if a.2.testBit 0 then Base.addRow (Base.timesT b) rest
      else rest

private theorem rowProductFrom_zero (b : Mat) (k : ℕ) :
    rowProductFrom (0, 0) b k = (0, 0) := by
  induction b generalizing k with
  | nil => rfl
  | cons b bs ih => simp [rowProductFrom, ih, Base.addRow]

private theorem rowProductFrom_div (a : Row) (b : Mat) (k : ℕ) :
    rowProductFrom (a.1 / 2, a.2 / 2) b k = rowProductFrom a b (k + 1) := by
  induction b generalizing k with
  | nil => rfl
  | cons b bs ih => simp only [rowProductFrom, Nat.testBit_div_two, ih]

set_option linter.unusedSimpArgs false in
theorem product_eq (a : Row) (b : Mat) : product a b = rowProduct a b := by
  change product a b = rowProductFrom a b 0
  induction b generalizing a with
  | nil => rfl
  | cons b bs ih =>
    by_cases h : a = (0, 0)
    · subst a
      simp only [product, if_true, rowProductFrom_zero]
    · rw [product, if_neg h, ih, rowProductFrom_div, rowProductFrom]
      cases h₀ : a.1.testBit 0 <;> cases h₁ : a.2.testBit 0 <;>
        simp [h₀, h₁, Base.addRow, Base.timesT, Nat.xor_assoc, xor_left_comm, xor_cancel]

/-- Check corresponding product rows, reading the lists once. -/
def checkRows : Mat → Mat → Mat → Bool
  | [], _, [] => true
  | a :: as, b, c :: cs => (product a b == c) && checkRows as b cs
  | _, _, _ => false

theorem checkRows_get (a b c : Mat) (h : checkRows a b c = true)
    (i : ℕ) (hi : i < a.length) : product (a.getD i (0, 0)) b = c.getD i (0, 0) := by
  induction a generalizing c i with
  | nil => simp at hi
  | cons a as ih =>
    cases c with
    | nil => simp [checkRows] at h
    | cons c cs =>
      simp only [checkRows, Bool.and_eq_true, beq_iff_eq] at h
      cases i with
      | zero => simpa using h.1
      | succ i => simpa using ih cs h.2 i (Nat.lt_of_succ_lt_succ hi)

theorem eval_product (n : ℕ) (a b c : Mat) (ha : a.length = n)
    (hb : b.length = n) (h : checkRows a b c = true) :
    eval n a * eval n b = eval n c := by
  apply Packed.eval_product n a b c hb
  intro i
  rw [← product_eq]
  exact checkRows_get a b c h i.val (ha ▸ i.isLt)

/-- Concatenate already checked blocks without repeating the computations. -/
theorem checkRows_append (a₁ a₂ b c₁ c₂ : Mat)
    (h₁ : checkRows a₁ b c₁ = true) (h₂ : checkRows a₂ b c₂ = true) :
    checkRows (a₁ ++ a₂) b (c₁ ++ c₂) = true := by
  induction a₁ generalizing c₁ with
  | nil => cases c₁ <;> simp_all [checkRows]
  | cons a as ih =>
    cases c₁ with
    | nil => simp [checkRows] at h₁
    | cons c cs =>
      simp only [checkRows, Bool.and_eq_true] at h₁
      simp only [List.cons_append, checkRows, h₁.1, Bool.true_and]
      exact ih cs h₁.2

/-- Check a row formula without repeatedly indexing its output list. -/
def checkFormula (f : ℕ → Row) : Mat → ℕ → Bool
  | [], _ => true
  | a :: as, k => (a == f k) && checkFormula f as (k + 1)

theorem checkFormula_get (f : ℕ → Row) (a : Mat) (k : ℕ)
    (h : checkFormula f a k = true) (i : ℕ) (hi : i < a.length) :
    a.getD i (0, 0) = f (k + i) := by
  induction a generalizing k i with
  | nil => simp at hi
  | cons a as ih =>
    simp only [checkFormula, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      simpa [Nat.add_assoc, Nat.add_comm 1] using
        ih (k + 1) h.2 i (Nat.lt_of_succ_lt_succ hi)

/-- Check an indexed binary row operation by simultaneous traversal. -/
def checkZip (f : ℕ → Row → Row → Row) : Mat → Mat → Mat → ℕ → Bool
  | [], [], [], _ => true
  | a :: as, b :: bs, c :: cs, k => (c == f k a b) && checkZip f as bs cs (k + 1)
  | _, _, _, _ => false

theorem checkZip_get (f : ℕ → Row → Row → Row) (a b c : Mat) (k : ℕ)
    (h : checkZip f a b c k = true) (i : ℕ) (hi : i < a.length) :
    c.getD i (0, 0) = f (k + i) (a.getD i (0, 0)) (b.getD i (0, 0)) := by
  induction a generalizing b c k i with
  | nil => simp at hi
  | cons a as ih =>
    cases b with
    | nil => simp [checkZip] at h
    | cons b bs =>
      cases c with
      | nil => simp [checkZip] at h
      | cons c cs =>
        simp only [checkZip, Bool.and_eq_true, beq_iff_eq] at h
        cases i with
        | zero => simpa using h.1
        | succ i =>
          simpa [Nat.add_assoc, Nat.add_comm 1] using
            ih bs cs (k + 1) h.2 i (Nat.lt_of_succ_lt_succ hi)

/-- Assemble a finite check from a first block and the remaining rows. -/
theorem checkRows_split (a b c : Mat) (m : ℕ)
    (h₁ : checkRows (a.take m) b (c.take m) = true)
    (h₂ : checkRows (a.drop m) b (c.drop m) = true) : checkRows a b c = true := by
  have h := checkRows_append (a.take m) (a.drop m) b (c.take m) (c.drop m) h₁ h₂
  simpa only [List.take_append_drop] using h

/-- The elementary packed row for the identity matrix. -/
def unitRow (i : ℕ) : Row := (2 ^ i, 0)

theorem decode_unitRow (i j : ℕ) : decode (unitRow i) j = if i = j then 1 else 0 := by
  simp [unitRow, decode, Base.entry,
    Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
    Nat.testBit_two_pow]

theorem decode_diagonal (i j : ℕ) :
    decode (2 ^ i, 2 ^ i) j = (omega ^ 2) * (if i = j then 1 else 0) := by
  by_cases h : i = j
  · simp [decode, Base.entry,
      Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
      h, omega_sq, add_comm]
  · simp [decode, Base.entry,
      Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
      h]

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
