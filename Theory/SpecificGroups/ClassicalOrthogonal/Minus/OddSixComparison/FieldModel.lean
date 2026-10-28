module

public import Theory.FieldTheory.QuadraticFrobeniusFixed
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag

/-!
# The actual coefficient field for the minus-six/unitary-four comparison

For q = pⁿ, n > 0, the matrices have coefficients in GF(p^(2n)).
The antidiagonal Hermitian form uses the actual pⁿ-power automorphism,
whose fixed field has q elements. These witnesses retain the unitary
parameter convention of Aschbacher–Smith A.2.17, footnote 3 on printed
p.38, and GLS3 §2.7. No group comparison is asserted here.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison
open BenderSuzuki.MatrixGroups Theory.SpecificGroups.ClassicalUnitary

variable (p n : ℕ) [Fact p.Prime]

/-- The actual quadratic-extension coefficient field. -/
abbrev Extension := GaloisField p (2 * n)

/-- The q-power automorphism, where q = pⁿ. -/
def conjugation : Extension p n ≃+* Extension p n :=
  iterateFrobeniusEquiv (Extension p n) p n

/-- The actual fixed subfield of the displayed Frobenius. -/
def fixedField : Subfield (Extension p n) :=
  FixedBy.subfield (Extension p n) (conjugation p n)

variable [NeZero n]

/-- Matrix coefficients lie in a field of order q². -/
theorem card_extension : Nat.card (Extension p n) = (p ^ n) ^ 2 := by
  rw [GaloisField.card p (2 * n) (Nat.mul_ne_zero (by decide) (NeZero.ne n)),
    ← pow_mul, Nat.mul_comm n 2]

/-- The fixed-field order is exactly the intended unitary parameter. -/
theorem card_fixedField : Nat.card (fixedField p n) = p ^ n :=
  GaloisField.card_fixedBy_quadraticFrobenius p n (NeZero.ne n)

/-- Quadratic Frobenius is an involution on this actual coefficient field. -/
theorem conjugation_involutive : Function.Involutive (conjugation p n) := by
  intro x
  change iterateFrobeniusEquiv (Extension p n) p n
    (iterateFrobeniusEquiv (Extension p n) p n x) = x
  rw [← iterateFrobeniusEquiv_add_apply, iterateFrobeniusEquiv_def, ← two_mul]
  rw [← GaloisField.card p (2 * n) (Nat.mul_ne_zero (by decide) (NeZero.ne n))]
  let : Fintype (Extension p n) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card x

/-- The antidiagonal Hermitian form on the four-dimensional coefficient space. -/
def unitaryForm : HermitianForm 4 (Extension p n) :=
  UnitaryFourFlag.form (Extension p n) (conjugation p n) (conjugation_involutive p n)

@[simp] theorem unitaryForm_conj (x : Extension p n) :
    (unitaryForm p n).conj x = x ^ (p ^ n) :=
  iterateFrobeniusEquiv_def _ _ _ _

end ClassicalOrthogonal.Minus.OddSixComparison
