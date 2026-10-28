module
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.Certificate
public import Mathlib.Algebra.BigOperators.Fin
/-!
# Natural-number certificates for square coordinates

A recursive natural-number sum computes one coordinate of a square of a
base-seven row matrix. Casting the sum into `ZMod 7` gives the matrix coordinate;
a nonzero remainder therefore certifies that the square is not scalar.

The proof follows the recursive dot-product cast argument in
`Two/Enumeration/WordValues/Arithmetic.lean`. The input matrices and their ATLAS
attribution remain in `Fusion/MatrixData*.lean` and `Two/source/`.
-/

namespace ONan.Simplicity.TwoCertificate.Fusion.SquareExclusions
open scoped BigOperators
@[expose] public def sumNat (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => sumNat f n + f n
private theorem sumNat_cast (f : ℕ → ℕ) (n : ℕ) :
    (sumNat f n : ZMod 7) = ∑ k : Fin n, (f k.val : ZMod 7) := by
  induction n with
  | zero => simp [sumNat]
  | succ n ih => simp [sumNat, Nat.cast_add, ih, Fin.sum_univ_castSucc]
@[expose] public def squareEntry (rows : Fin 45 → ℕ) (c : Fin 45) : ℕ :=
  sumNat (fun k => (rows 0 / 7^k % 7) * (rows (Fin.ofNat 45 k) / 7^c.val % 7)) 45
private theorem squareEntry_cast (rows : Fin 45 → ℕ) (c : Fin 45) :
    (squareEntry rows c : ZMod 7) = (FusionData.decodeRows rows ^ 2) 0 c := by
  rw [squareEntry, sumNat_cast, pow_two, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hk : Fin.ofNat 45 k.val = k := by ext; exact Nat.mod_eq_of_lt k.isLt
  simp only [hk, Nat.cast_mul, FusionData.decodeRows]
public theorem squareEntry_ne (rows : Fin 45 → ℕ) (c : Fin 45)
    (h : squareEntry rows c % 7 ≠ 0) :
    (FusionData.decodeRows rows ^ 2) 0 c ≠ 0 := by
  rw [← squareEntry_cast]
  intro hz
  have hv := congrArg ZMod.val hz
  exact h (by simpa using hv)
/-- Each index is zero, a listed candidate, or has a nonscalar square. -/
@[expose] public def Covered (i : Fin 512) : Prop :=
  i = 0 ∨ (∃ t : Fin 87, vertex t = i) ∨
    ∃ row col : Fin 45, row ≠ col ∧ (FusionData.form i ^ 2) row col ≠ 0

end ONan.Simplicity.TwoCertificate.Fusion.SquareExclusions
