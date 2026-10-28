module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import ABG.ChapterII.Section2.UnitaryCard

/-!
# The full unitary plane over the field of nine elements

The entrywise isomorphism from `FiniteField.Nine` to `GaloisField 3 2`
intertwines quadratic conjugation with cube Frobenius. It therefore carries
exactly the identity-form isometry group to the original `ABG.GU2 3 1`
model. Its checked order formula gives order 96, excluding divisibility by
nine. The actual group equivalence is constructed before using the order.

This is the multiplicity-space bound for the anticommuting SU₄(3) lift
centralizer. Sources: GLS3 chapter 2, §2.3, for the unitary conventions;
ABG II.2 Lemma 1, article p.17, for the two-dimensional calculation;
Aschbacher–Smith, Theorem 0.1.2(4), printed p.4 of `refs/quasithin.pdf`,
for the local application.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Anticommuting

/-- The actual full identity-form unitary group in dimension two. -/
abbrev FullUnitaryTwo := (form 2).unitarySubgroup

private theorem coefficient_mem_iff (x : GL (Fin 2) FiniteField.Nine) :
    GeneralLinearGroup.map FiniteField.Nine.equivGaloisField.toRingHom x ∈
        (ABG.unitaryForm 2 3 1 (by decide)).unitarySubgroup ↔
      x ∈ (form 2).unitarySubgroup := by
  let e := FiniteField.Nine.equivGaloisField
  let J := ABG.unitaryForm 2 3 1 (by decide)
  rw [J.mem_unitarySubgroup_iff, (form 2).mem_unitarySubgroup_iff]
  have hadj : J.conjTranspose (GeneralLinearGroup.map e.toRingHom x).val =
      ((form 2).conjTranspose x.val).map e := by
    ext i j
    change e (x.val j i) ^ 3 = e (star (x.val j i))
    exact (FiniteField.Nine.equivGaloisField_star (x.val j i)).symm
  have hval : (GeneralLinearGroup.map e.toRingHom x).val = x.val.map e := rfl
  change J.conjTranspose (GeneralLinearGroup.map e.toRingHom x).val * 1 *
      (GeneralLinearGroup.map e.toRingHom x).val = 1 ↔
    (form 2).conjTranspose x.val * 1 * x.val = 1
  rw [hadj, hval]
  simp only [mul_one]
  rw [← Matrix.map_mul]
  have hone : (1 : Matrix (Fin 2) (Fin 2) FiniteField.Nine).map e = 1 :=
    Matrix.map_one e (map_zero e) (map_one e)
  rw [← hone]
  exact e.toEquiv.mapMatrix.injective.eq_iff

/-- The actual coefficient-field isomorphism carries the full unitary plane group. -/
noncomputable def fullUnitaryTwoEquiv : FullUnitaryTwo ≃* ABG.GU2 3 1 (by decide) where
  toFun x := ⟨GeneralLinearGroup.map FiniteField.Nine.equivGaloisField.toRingHom x.val,
    (coefficient_mem_iff x.val).2 x.property⟩
  invFun x := ⟨GeneralLinearGroup.map FiniteField.Nine.equivGaloisField.symm.toRingHom x.val, by
    apply (coefficient_mem_iff _).1
    have he : GeneralLinearGroup.map FiniteField.Nine.equivGaloisField.toRingHom
        (GeneralLinearGroup.map FiniteField.Nine.equivGaloisField.symm.toRingHom x.val) = x.val := by
      ext i j
      exact FiniteField.Nine.equivGaloisField.apply_symm_apply (x.val.val i j)
    rw [he]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    funext i j
    exact FiniteField.Nine.equivGaloisField.symm_apply_apply (x.val.val i j)
  right_inv x := by
    apply Subtype.ext
    apply Units.ext
    funext i j
    exact FiniteField.Nine.equivGaloisField.apply_symm_apply (x.val.val i j)
  map_mul' x y := Subtype.ext
    ((GeneralLinearGroup.map FiniteField.Nine.equivGaloisField.toRingHom).map_mul x.val y.val)

/-- The field-nine full unitary plane group has order 96. -/
theorem fullUnitaryTwo_card : Nat.card FullUnitaryTwo = 96 := by
  rw [Nat.card_congr fullUnitaryTwoEquiv.toEquiv]
  exact ABG.GU2_card 3 1 (by decide) (by decide)

/-- Nine does not divide the order of the full unitary plane group. -/
theorem fullUnitaryTwo_not_nine_dvd : ¬ 3 ^ 2 ∣ Nat.card FullUnitaryTwo := by
  rw [fullUnitaryTwo_card]
  decide

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Anticommuting
