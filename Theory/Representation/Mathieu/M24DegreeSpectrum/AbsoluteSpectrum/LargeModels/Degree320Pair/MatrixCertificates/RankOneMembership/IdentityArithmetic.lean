module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneMembership.Arithmetic
/-!
# Sequential identity-row certificate

Checking the powers of two in order certifies the identity matrix without
reducing a list produced by `List.ofFn`. The concrete consumer is
`Numerics.ident_matrix` on the stored identity rows.
-/
@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneChecks
open Thompson.BinaryMatrix

def checkIdentity : List Nat → Nat → Bool
  | [], _ => true
  | x :: xs, k => (x == 2 ^ k) && checkIdentity xs (k + 1)

theorem checkIdentity_get (a : List Nat) (k : Nat) (h : checkIdentity a k = true)
    (i : Nat) (hi : i < a.length) : a[i]! = 2 ^ (k + i) := by
  induction a generalizing k i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [checkIdentity, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      simpa only [List.getElem!_cons_succ, Nat.add_right_comm, Nat.add_assoc] using
        ih (k + 1) h.2 i (Nat.lt_of_succ_lt_succ hi)

theorem one_sound (n : Nat) (a : List Nat) (ha : a.length = n)
    (h : checkIdentity a 0 = true) : decode n a.toArray = 1 := by
  ext i j
  have hh := checkIdentity_get a 0 h i.val (by simpa only [ha] using i.isLt)
  simp only [Nat.zero_add] at hh
  simp [decode, hh, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneChecks
