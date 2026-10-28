module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RowArithmetic

/-!
# Sparse row certificates for the literal degree-320 trace products

A gap list encodes a binary mask by counting zero bits before each successive
set bit. The identity `skipRow_pow_two` skips an entire run of zeros, and
`gapRow_eq` then proves the sparse row sum equals the original computation.
The checker also verifies reconstruction of every input mask. Explicit
transport of list drops assembles bounded blocks without recomputing products.

The concrete consumers are the twenty `Product` modules in this directory.
Data provenance is in `../../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows

def gapMask : List Nat → Nat
  | [] => 0
  | k :: ks => 2 ^ k * (2 * gapMask ks + 1)

def gapRow (b : List Nat) : List Nat → Nat
  | [] => 0
  | k :: ks => match b.drop k with
    | [] => 0
    | v :: vs => v ^^^ gapRow vs ks

theorem skipRow_zero (b : List Nat) : skipRow 0 b = 0 := by
  induction b <;> simp [skipRow, *]

theorem skipRow_double (a b : Nat) (bs : List Nat) :
    skipRow (2*a) (b::bs) = skipRow a bs := by
  simp [skipRow]

theorem skipRow_pow_two (a k : Nat) (b : List Nat) :
    skipRow (2^k*a) b = skipRow a (b.drop k) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    cases b with
    | nil => rfl
    | cons b bs =>
      rw [show 2^(k+1)*a = 2*(2^k*a) by rw [pow_succ]; ac_rfl, skipRow_double]
      exact ih bs

theorem gapRow_eq (b : List Nat) (ks : List Nat) :
    gapRow b ks = skipRow (gapMask ks) b := by
  induction ks generalizing b with
  | nil => simp [gapRow, gapMask, skipRow_zero]
  | cons k ks ih =>
    rw [gapMask, skipRow_pow_two]
    simp only [gapRow]
    cases hb : b.drop k with
    | nil => rfl
    | cons v vs =>
      change v ^^^ gapRow vs ks = _
      rw [ih]
      simp [skipRow, Nat.add_div]

def checkGaps : List Nat → List Nat → List Nat → List (List Nat) → Bool
  | [], _, [], [] => true
  | a :: as, b, c :: cs, ks :: kss =>
      (gapMask ks == a) && (gapRow b ks == c) && checkGaps as b cs kss
  | _, _, _, _ => false

theorem checkGaps_sound (a b c : List Nat) (gs : List (List Nat))
    (h : checkGaps a b c gs = true) : checkSkip a b c = true := by
  induction a generalizing c gs with
  | nil => cases c <;> cases gs <;> simp_all [checkSkip, checkGaps]
  | cons a as ih =>
    cases c with
    | nil => simp [checkGaps] at h
    | cons c cs =>
      cases gs with
      | nil => simp [checkGaps] at h
      | cons g gs =>
        simp only [checkGaps, Bool.and_eq_true, beq_iff_eq] at h
        simp only [checkSkip, Bool.and_eq_true, beq_iff_eq]
        exact ⟨by rw [← h.1.1, ← gapRow_eq]; exact h.1.2, ih cs gs h.2⟩

theorem step (a b c : List Nat) (gs : List (List Nat)) (i n : Nat)
    (h₁ : checkGaps ((a.drop i).take n) b ((c.drop i).take n)
      gs = true)
    (h₂ : checkRows (a.drop (i+n)) b (c.drop (i+n)) = true) :
    checkRows (a.drop i) b (c.drop i) = true := by
  apply checkRows_split _ _ _ n
    (checkRows_of_skip _ _ _ (checkGaps_sound _ _ _ _ h₁))
  simpa only [List.drop_drop, Nat.add_comm] using h₂

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows
