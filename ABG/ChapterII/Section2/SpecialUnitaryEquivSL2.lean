module
public import ABG.ChapterII.Section2.UnitaryQuadraticCoordinates
public import BenderSuzuki.MatrixGroups.SpecialUnitaryFixedEquiv
public import GorensteinWalter.LinearRingEquiv
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Ring.Action.End

/-!
# The actual special unitary group in dimension two

For odd p and nonzero n, the special subgroup of the original identity-Gram
unitary form over GF(p^(2n)) is isomorphic to SL2 over GF(p^n). This proves
ABG Chapter II, Section 2, Lemma 1(vi), article page 17
(`refs/latex/alperin-brauer-gorenstein-pages/page-018.tex`), for use in the
unitary central-product models and Section 3, Proposition 3. The fields of
orders three and nine are included.

The quadratic-coordinate theorem supplies z with z*conj(z)=-1, a nonzero t
with conj(t)=-t, and an equivalence from the actual fixed subfield to GF(p^n).
The explicit basis matrix C=[[1,t],[z,-zt]] is invertible and changes the
Hermitian Gram matrix to 2t times the standard alternating matrix. A direct
two-by-two determinant calculation shows that a determinant-one matrix
preserves this new form exactly when all its entries lie in the fixed field.
Conjugation by C therefore gives a bijective group homomorphism from SL2 of
that fixed field onto the actual special unitary subgroup. The existing
coefficient-ring equivalence completes the construction. All intermediate
matrix calculations retain the given form and its stored involution; the
shared Hermitian basis-conjugation criterion supplies the change-of-form step.
-/

open Matrix
open scoped Matrix
open BenderSuzuki.MatrixGroups

namespace ABG

/-- The actual standard special unitary two-dimensional group is SL2 over GF(p^n). -/
public noncomputable def specialUnitaryTwo_equiv_sl2
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0) :
    (unitaryForm 2 p n hn).specialSubgroup ≃*
      SpecialLinearGroup (Fin 2) (GaloisField p n) := by
  classical
  apply Classical.choice
  obtain ⟨⟨z, t, hz, ht0, ht⟩, ⟨e⟩⟩ := unitaryQuadraticCoordinates p n hp hn
  have hp2 : p ≠ 2 := by
    intro h
    obtain ⟨k, hk⟩ := hp
    omega
  have h2 : (2 : GaloisField p (2 * n)) ≠ 0 := by
    exact_mod_cast CharP.cast_ne_zero_of_ne_of_prime
      (GaloisField p (2 * n)) Nat.prime_two hp2
  obtain ⟨C, _, hC⟩ := HermitianForm.exists_skew_basis (unitaryForm 2 p n hn) rfl h2 z t hz ht0 ht
  exact ⟨(HermitianForm.specialUnitaryEquivFixed (unitaryForm 2 p n hn) C (2 * t)
    (mul_ne_zero h2 ht0) hC).trans (GorensteinWalter.sl2RingEquiv e)⟩

end ABG
