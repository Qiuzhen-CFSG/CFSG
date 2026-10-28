module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RowArithmetic
/-!
# Bounded row certificates for the degree-320 ATLAS relations

A product certificate is split into eight-row blocks. Concatenation joins the
kernel-checked blocks, and the existing packed multiplication theorem interprets
them as literal matrix products. This keeps each kernel reduction bounded.

Source: John Bray, ATLAS presentation M24G1-P1; the unchanged degree-320
matrix files are documented in `Degree320Pair/source/README.md`.
-/

@[expose] public section
open Thompson.BinaryMatrix
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate

/-- A proposition with an inert head, so joining certificates does not ask
conversion to evaluate a closed matrix-product checker. -/
structure Checked (a b c : List Nat) : Prop where
  eq_true : checkRows a b c = true

/-- Connect adjacent row blocks with all arithmetic indices still symbolic. -/
theorem step (k : Nat) (a b c : List Nat)
    (h : Checked ((a.drop (8*k)).take 8) b ((c.drop (8*k)).take 8))
    (ht : Checked (a.drop (8*(k+1))) b (c.drop (8*(k+1)))) :
    Checked (a.drop (8*k)) b (c.drop (8*k)) := by
  refine ⟨MatrixCertificates.checkRows_split (a.drop (8*k)) b (c.drop (8*k)) 8 h.eq_true ?_⟩
  simpa only [List.drop_drop, Nat.mul_add, Nat.mul_one] using ht.eq_true

/-- Remove the zero drop after the final block connection. -/
theorem start (a b c : List Nat)
    (h : Checked (a.drop (8*0)) b (c.drop (8*0))) : Checked a b c := by
  simpa only [Nat.mul_zero, List.drop_zero] using h

/-- The packed rows of the identity matrix. -/
def identityRows : List Nat := List.ofFn (fun i : Fin 320 => 2 ^ i.val)

theorem decode_identityRows : decode 320 identityRows.toArray = 1 := by
  ext i j
  simp [decode, identityRows, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff, -List.ofFn_succ]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate
