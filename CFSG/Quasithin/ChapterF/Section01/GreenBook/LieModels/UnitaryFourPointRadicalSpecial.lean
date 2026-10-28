module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointRadicalSpecial
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointLocal

/-!
# The special point radical in the standard unitary-four model

For q = 2^n, n ≥ 1, the middle-block kernel in the vector stabilizer is a
special two-group of order q^5, with center of order q. The stored quadratic
Frobenius is nontrivial because its fixed field has order q, whereas the
matrix field has order q². The coordinate results then identify the center,
derived subgroup and Frattini subgroup.

This is the special-group structure denoted q^(1+4) in Aschbacher--Smith,
F.1.11 and F.1.12(I)(6), printed pp. 262--263 of `refs/quasithin.pdf`.
Identification of this kernel with O₂ of the local group is separate.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal
open Theory.SpecificGroups.ClassicalUnitary
variable (n : ℕ) (hn : 1 ≤ n)

include hn in
/-- The stored quadratic Frobenius is not the identity, including when q = 2. -/
theorem fieldConj_nontrivial : ∃ u : MatrixField n, fieldConj n u ≠ u := by
  by_contra! h
  let e : FixedField n ≃ MatrixField n :=
    { toFun := Subtype.val
      invFun := fun u => ⟨u, h u⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Nat.card_congr e
  rw [fixedField_card n hn, matrixField_card n hn] at he
  have hq : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
  nlinarith

/-- The actual matrix radical has center equal to its derived subgroup. -/
theorem radical_center_eq_commutator :
    Subgroup.center (Radical n hn) = commutator (Radical n hn) :=
  (UnitaryFourPointLocal.commutator_radical_eq_center _ _ _
    (fieldConj_nontrivial n hn)).symm

/-- The actual matrix radical has center equal to its Frattini subgroup. -/
theorem radical_center_eq_frattini :
    Subgroup.center (Radical n hn) = frattini (Radical n hn) :=
  (UnitaryFourPointLocal.frattini_radical_eq_center _ _ _
    (fieldConj_nontrivial n hn) (radical_isTwoGroup n hn)).symm

/-- The center has order q, rather than the matrix-field order q². -/
theorem radical_center_card : Nat.card (Subgroup.center (Radical n hn)) = 2 ^ n := by
  exact (UnitaryFourPointLocal.center_radical_card (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn) (fieldConj_nontrivial n hn)).trans (fixedField_card n hn)

/-- The full special-group and order assertions for the constructed point radical. -/
theorem radical_special :
    IsPGroup 2 (Radical n hn) ∧
    Subgroup.center (Radical n hn) = commutator (Radical n hn) ∧
    Subgroup.center (Radical n hn) = frattini (Radical n hn) ∧
    Nat.card (Radical n hn) = (2 ^ n) ^ 5 ∧
    Nat.card (Subgroup.center (Radical n hn)) = 2 ^ n :=
  ⟨radical_isTwoGroup n hn, radical_center_eq_commutator n hn,
    radical_center_eq_frattini n hn, radical_card n hn, radical_center_card n hn⟩

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal
