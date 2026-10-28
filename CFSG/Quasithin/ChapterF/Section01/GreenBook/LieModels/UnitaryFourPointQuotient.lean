module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointLocal
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient

/-!
# The unitary-four point-local quotient and exact two-core

Over GF(q²), q = 2^n with n ≥ 1, the vector stabilizer modulo the previously
constructed radical is PSL₂ over the actual Frobenius fixed field of order q.
The quotient has trivial two-core, including q = 2. Since the radical is a
normal two-group of order q^5, it is exactly the two-core. The diagonal Levi
section is retained as an actual matrix homomorphism for the residual proofs.

This establishes the first quotient and two-core identification needed for
Aschbacher--Smith F.1.12(I)(6), printed pp. 263--264 of `refs/quasithin.pdf`.
The special-group and residual assertions are separate results.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal

open Theory.SpecificGroups.ClassicalUnitary

variable (n : ℕ) (hn : 1 ≤ n)

/-- The middle-block quotient action on the fixed-field two-space. -/
def middleSL : MatrixLocal n hn →* Matrix.SpecialLinearGroup (Fin 2) (FixedField n) :=
  UnitaryFourPointQuotient.middleSL (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn)

/-- The literal diagonal Levi section; its matrix formula is `leviSL_val`. -/
def leviSection : Matrix.SpecialLinearGroup (Fin 2) (FixedField n) →* MatrixLocal n hn :=
  UnitaryFourPointQuotient.leviSL (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn)

@[simp] theorem middleSL_leviSection (B : Matrix.SpecialLinearGroup (Fin 2) (FixedField n)) :
    middleSL n hn (leviSection n hn B) = B :=
  UnitaryFourPointQuotient.middleSL_leviSL _ _ _ B

/-- The quotient is PSL₂ over the actual fixed subfield, of order `2^n`. -/
def quotientEquivPSL : (MatrixLocal n hn ⧸ Radical n hn) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (FixedField n) :=
  UnitaryFourPointQuotient.quotientEquivPSL (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn)

/-- The equivalent special-linear realization, including the binary case. -/
def quotientEquivSL : (MatrixLocal n hn ⧸ Radical n hn) ≃*
    Matrix.SpecialLinearGroup (Fin 2) (FixedField n) :=
  UnitaryFourPointQuotient.quotientEquivSL (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn)

theorem quotient_twoCore_eq_bot : pCore 2 (MatrixLocal n hn ⧸ Radical n hn) = ⊥ :=
  UnitaryFourPointQuotient.quotient_twoCore_eq_bot (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn)

/-- The entire middle-block kernel is the two-core of the vector stabilizer. -/
theorem radical_eq_twoCore : Radical n hn = pCore 2 (MatrixLocal n hn) :=
  UnitaryFourPointQuotient.radical_eq_twoCore (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn) (radical_isTwoGroup n hn)

/-- The source quotient uses O₂ itself, not merely a candidate subgroup. -/
def quotientByTwoCoreEquivPSL : (MatrixLocal n hn ⧸ pCore 2 (MatrixLocal n hn)) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (FixedField n) :=
  (QuotientGroup.quotientMulEquivOfEq (radical_eq_twoCore n hn).symm).trans
    (quotientEquivPSL n hn)

theorem twoCore_card : Nat.card (pCore 2 (MatrixLocal n hn)) = (2 ^ n) ^ 5 := by
  rw [← radical_eq_twoCore, radical_card]

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal
