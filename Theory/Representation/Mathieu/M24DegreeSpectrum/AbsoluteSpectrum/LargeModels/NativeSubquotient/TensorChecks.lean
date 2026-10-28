module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.TensorRows

/-!
# Linear traversal of the saved native tensor rows

The checker advances through the saved rows once, avoiding repeated indexing
into the large ambient matrix. The soundness theorem supplies the exact premise
of `tensorMatrix_of_rows`. The first consumer is the native 1792 quotient.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient
open Packed Degree220Pair.NativeActions.CertificatePacked

/-- Transposition commutes with the row-major tensor coordinates. -/
theorem tensorMatrix_transpose {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) (ZMod 2))
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (TensorCoordinates.tensorMatrix A B).transpose =
      TensorCoordinates.tensorMatrix A.transpose B.transpose := rfl

def checkTensorRows (width count : ℕ) (a b : List ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | x::xs, start => (tensorRow width count a[start/width]! b[start%width]! == x) &&
      checkTensorRows width count a b xs (start+1)

theorem checkTensorRows_sound (width count : ℕ) (a b rows : List ℕ) (start : ℕ)
    (h : checkTensorRows width count a b rows start = true)
    (i : ℕ) (hi : i < rows.length) :
    tensorRow width count a[(start+i)/width]! b[(start+i)%width]! = rows[i]! := by
  induction rows generalizing start i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [checkTensorRows, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
        simpa [Nat.add_assoc, Nat.add_comm 1] using
          ih (start+1) h.2 i (by simpa using hi)

/-- Checked packed rows identify the genuine row-major tensor matrix. -/
theorem tensorMatrix_of_check {m n : ℕ} (a b rows : List ℕ)
    (hb : ∀ i : Fin n, b[i.val]! < 2^n)
    (hlen : rows.length = m*n)
    (hc : checkTensorRows n m a b rows 0 = true) :
    TensorCoordinates.tensorMatrix (matrix m m a) (matrix n n b) =
      matrix (m*n) (m*n) rows := by
  apply tensorMatrix_of_rows (m := m) (n := n) a b rows hb
  intro i
  simpa only [Nat.zero_add, Fin.coe_divNat, Fin.coe_modNat] using
    checkTensorRows_sound n m a b rows 0 hc i.val (by rw [hlen]; exact i.isLt)
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient
