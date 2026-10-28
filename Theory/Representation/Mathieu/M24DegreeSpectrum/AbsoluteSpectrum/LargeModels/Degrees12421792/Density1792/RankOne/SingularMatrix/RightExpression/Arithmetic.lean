module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.Arithmetic

/-!
# Bounded certificates for the right singular expression

Sequential blocks compose to the original carry-free checker. Optional explicit
integer sums separate selected-row addition from parity reduction; the sums are
checked, never trusted. The matrix interpretation is the existing `Wide` checker.
The concrete consumer is `RightExpression.Conditional` on the unchanged ATLAS rows.
See `source/README.md` for the five-product factorization and data provenance.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.RightCertificate

open Thompson.BinaryMatrix

def diagRows (n : Nat) : List Nat := List.ofFn (fun i : Fin n => 2 ^ i.val)

theorem decode_diagRows (n : Nat) : decode n (diagRows n).toArray = 1 := by
  ext i j
  simp [decode, diagRows, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

/-- Packed rowwise XOR is precisely addition of the decoded matrices. -/
theorem decode_zipWith_xor (n : Nat) (a b : List Nat)
    (ha : a.length = n) (hb : b.length = n) :
    decode n (List.zipWith Nat.xor a b).toArray =
      decode n a.toArray + decode n b.toArray := by
  ext i j
  simp [decode, getElem!_pos, ha, hb, bit_xor]

theorem product_step (a w c : List Nat) (i k : Nat)
    (h₁ : Wide.checkRows 1792 ((a.drop i).take k) w ((c.drop i).take k) = true)
    (h₂ : Wide.checkRows 1792 (a.drop (i+k)) w (c.drop (i+k)) = true) :
    Wide.checkRows 1792 (a.drop i) w (c.drop i) = true := by
  have h := Wide.checkRows_append 1792 ((a.drop i).take k) ((a.drop i).drop k)
    w ((c.drop i).take k) ((c.drop i).drop k) h₁
    (by simpa only [List.drop_drop, Nat.add_comm] using h₂)
  simpa only [List.take_append_drop] using h

theorem spread_append (a₁ a₂ w₁ w₂ : List Nat)
    (h₁ : Wide.checkSpreadRows 1792 a₁ w₁ = true)
    (h₂ : Wide.checkSpreadRows 1792 a₂ w₂ = true) :
    Wide.checkSpreadRows 1792 (a₁ ++ a₂) (w₁ ++ w₂) = true := by
  induction a₁ generalizing w₁ with
  | nil => cases w₁ <;> simp_all [Wide.checkSpreadRows]
  | cons x xs ih =>
    cases w₁ with
    | nil => simp [Wide.checkSpreadRows] at h₁
    | cons y ys =>
      simp only [Wide.checkSpreadRows, Bool.and_eq_true] at h₁
      simp only [List.cons_append, Wide.checkSpreadRows, Bool.and_eq_true]
      exact ⟨h₁.1, ih _ h₁.2⟩

theorem spread_step (a w : List Nat) (i k : Nat)
    (h₁ : Wide.checkSpreadRows 1792 ((a.drop i).take k) ((w.drop i).take k) = true)
    (h₂ : Wide.checkSpreadRows 1792 (a.drop (i+k)) (w.drop (i+k)) = true) :
    Wide.checkSpreadRows 1792 (a.drop i) (w.drop i) = true := by
  have h := spread_append ((a.drop i).take k) ((a.drop i).drop k)
    ((w.drop i).take k) ((w.drop i).drop k) h₁
    (by simpa only [List.drop_drop, Nat.add_comm] using h₂)
  simpa only [List.take_append_drop] using h

/-- A single row can be certified by two independent reductions, keeping the
integer sum out of the parity reduction. -/
theorem product_cons (a c s : Nat) (as w cs : List Nat)
    (hs : Wide.sumRow a w = s) (hp : Wide.checkParity 1792 s c = true)
    (ht : Wide.checkRows 1792 as w cs = true) :
    Wide.checkRows 1792 (a :: as) w (c :: cs) = true := by
  simp only [Wide.checkRows, Bool.and_eq_true]
  exact ⟨by rw [hs]; exact hp, ht⟩

/-- Check supplied integer sums before using their digit parities. -/
def checkWitnessRows : List Nat → List Nat → List Nat → List Nat → Bool
  | [], _, [], [] => true
  | a :: as, w, c :: cs, s :: ss =>
      (Wide.sumRow a w == s) && Wide.checkParity 1792 s c && checkWitnessRows as w cs ss
  | _, _, _, _ => false

theorem checkWitnessRows_sound (a w c s : List Nat)
    (h : checkWitnessRows a w c s = true) : Wide.checkRows 1792 a w c = true := by
  induction a generalizing c s with
  | nil => cases c <;> cases s <;> simp_all [checkWitnessRows, Wide.checkRows]
  | cons a as ih =>
    cases c with
    | nil => simp [checkWitnessRows] at h
    | cons c cs =>
      cases s with
      | nil => simp [checkWitnessRows] at h
      | cons s ss =>
        simp only [checkWitnessRows, Bool.and_eq_true, beq_iff_eq] at h
        exact product_cons a c s as w cs h.1.1 h.1.2 (ih cs ss h.2)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.RightCertificate
