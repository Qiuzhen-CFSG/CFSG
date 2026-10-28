module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.Packed
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Arithmetic

/-!
# Structural tensor rows and sparse rectangular intertwiners

A tensor row is a concatenation of copies of the second factor row, selected
by bits of the first factor. The bit lemma reduces a tensor coordinate check
to the small factors. Sparse gap lists reuse the proved degree-320 arithmetic;
both masks are reconstructed before their row products are compared.
These checks certify the native large-model embeddings and quotients.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Packed
open Degree220Pair.NativeActions.CertificatePacked
open Degree320Pair.MatrixCertificates.TraceRows

/-- Concatenate `count` blocks of `width` bits in increasing column order. -/
def tensorRow (width : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | count+1, a, b => 2^width * tensorRow width count (a/2) b +
      (if a.testBit 0 then b else 0)

theorem tensorRow_bit (width count a b q r : ℕ) (hb : b < 2^width)
    (hq : q < count) (hr : r < width) :
    (tensorRow width count a b).testBit (q*width+r) =
      (a.testBit q && b.testBit r) := by
  induction count generalizing a q with
  | zero => omega
  | succ count ih =>
    rw [tensorRow, Nat.testBit_two_pow_mul_add _ (show (if a.testBit 0 then b else 0) < 2^width by
      split <;> simp_all)]
    cases q with
    | zero => cases a.testBit 0 <;> simp [hr]
    | succ q =>
      have hn : ¬ q.succ * width + r < width := by simp only [Nat.succ_mul]; omega
      have he : q.succ * width + r - width = q * width + r := by simp only [Nat.succ_mul]; omega
      simp only [hn, ↓reduceIte, he]
      rw [ih (a/2) q (by omega), Nat.testBit_div_two]

private theorem combine_eq_shift (a : ℕ) (b : List ℕ) :
    combine b a = Degree320Pair.shiftRow a b := by
  induction b generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [combine, Degree320Pair.shiftRow, ih]

theorem gapRow_combine (b : List ℕ) (g : List ℕ) :
    gapRow b g = combine b (gapMask g) := by
  rw [gapRow_eq, Degree320Pair.MatrixCertificates.skipRow_eq, combine_eq_shift]

/-- Reconstruct both left masks and compare the two sparse row products. -/
def checkIntertwiner (ys ws : List ℕ) :
    List ℕ → List ℕ → List (List ℕ) → List (List ℕ) → Bool
  | [], [], [], [] => true
  | x::xs, z::zs, a::as, b::bs =>
      (gapMask a == x) && (gapMask b == z) && (gapRow ys a == gapRow ws b) &&
        checkIntertwiner ys ws xs zs as bs
  | _, _, _, _ => false

theorem checkIntertwiner_sound (ys ws xs zs : List ℕ) (as bs : List (List ℕ))
    (h : checkIntertwiner ys ws xs zs as bs = true) :
    checkEqualProducts ys ws xs zs = true := by
  induction xs generalizing zs as bs with
  | nil => cases zs <;> cases as <;> cases bs <;> simp_all [checkIntertwiner, checkEqualProducts]
  | cons x xs ih =>
    cases zs with
    | nil => simp [checkIntertwiner] at h
    | cons z zs =>
      cases as with
      | nil => simp [checkIntertwiner] at h
      | cons a as =>
        cases bs with
        | nil => simp [checkIntertwiner] at h
        | cons b bs =>
          simp only [checkIntertwiner, Bool.and_eq_true, beq_iff_eq] at h
          simp only [checkEqualProducts, Bool.and_eq_true, beq_iff_eq]
          refine ⟨?_, ih zs as bs h.2⟩
          rw [← h.1.1.1, ← h.1.1.2, ← gapRow_combine, ← gapRow_combine]
          exact h.1.2

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Packed
