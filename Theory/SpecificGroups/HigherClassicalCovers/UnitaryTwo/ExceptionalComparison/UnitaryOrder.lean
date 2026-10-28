module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.Model
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.UnitaryOrder.Counting
public import Mathlib.GroupTheory.Index

/-!
# The exact order of the full special unitary group SU₄(2)

The full unitary group of the identity Hermitian form over `GoldenFour` has
order 77760 by orthonormal-column counting. Its actual determinant homomorphism
to `GoldenFourˣ` is surjective: a nonzero scalar has norm one, and the scalar
matrix `c • 1` has determinant `c⁴ = c`. The kernel is identified with the
literal `StandardSU`, including the inverse construction from every
unitary matrix of determinant one. Since the scalar group has order three,
`StandardSU` has order 25920.

This discharges precisely the unitary order premise in
`ExceptionalComparison.specialEquivPSp_of_bounds` and
`standardEquivPSp_of_bounds`, used for the U₄(2) row of Aschbacher–Smith
I.1.4(1), printed p.408 (`refs/quasithin.pdf`). The independent presentation
bound and final exceptional-isomorphism assembly remain with those consumers.

The forgetful homomorphism below is adapted from the retained
`CFSG/Quasithin/Chapter13/Section06/TerminalContradiction/Components/SuzukiIsolation/SmallGlobal/UnitaryTwo.lean`.
The orthonormal-column proof is extracted separately in `UnitaryOrder.Counting`.
-/

noncomputable section

open Matrix Atlas.Algebra
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.UnitaryOrder

abbrev F := GoldenFour
abbrev U := Matrix.unitaryGroup (Fin 4) F

def determinant : U →* Fˣ := Matrix.GeneralLinearGroup.det.comp Unitary.toUnits

theorem determinant_val (A : U) :
    (determinant A).val = Matrix.det A.val := rfl

def specialToUnitary : StandardSU →* U where
  toFun A := ⟨A.val.val, by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    have h := ((standardForm.mem_specialSubgroup_iff A.val).mp A.property).1
    change star A.val.val * 1 * A.val.val = 1 at h
    simpa only [mul_one] using h⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem specialToUnitary_injective : Function.Injective specialToUnitary := by
  intro A B h
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val h

theorem special_det (A : StandardSU) : Matrix.det A.val.val = (1 : F) := by
  have hd : Matrix.GeneralLinearGroup.det A.val = 1 :=
    ((standardForm.mem_specialSubgroup_iff A.val).mp A.property).2
  simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
    congrArg (fun c : Fˣ => c.val) hd

def specialToKernel : StandardSU →* determinant.ker :=
  specialToUnitary.codRestrict determinant.ker (fun A => by
    change determinant (specialToUnitary A) = 1
    apply Units.ext
    rw [determinant_val]
    exact special_det A)

def specialEquivKernel : StandardSU ≃* determinant.ker :=
  MulEquiv.ofBijective specialToKernel
    ⟨fun A B h => specialToUnitary_injective (congrArg Subtype.val h), by
      intro A
      refine ⟨⟨Unitary.toUnits A.val, ?_⟩, ?_⟩
      · apply (standardForm.mem_specialSubgroup_iff _).mpr
        constructor
        · change star A.val.val * 1 * A.val.val = 1
          simpa only [mul_one] using (Matrix.mem_unitaryGroup_iff'.mp A.val.property)
        · exact A.property
      · rfl⟩

theorem scalar_norm (c : Fˣ) : star (c : F) * (c : F) = 1 := by
  have h : ∀ x : F, x ≠ 0 → star x * x = 1 := by decide +kernel
  exact h c c.ne_zero

def scalar (c : Fˣ) : U :=
  ⟨(c : F) • (1 : Matrix (Fin 4) (Fin 4) F), by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    simp only [star_smul, star_one, smul_mul_smul_comm, one_mul,
      scalar_norm, one_smul]⟩

theorem determinant_scalar (c : Fˣ) : determinant (scalar c) = c := by
  apply Units.ext
  change Matrix.det ((c : F) • (1 : Matrix (Fin 4) (Fin 4) F)) = (c : F)
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  have h : ∀ x : F, x ^ 4 = x := by decide +kernel
  exact h c

theorem determinant_surjective : Function.Surjective determinant :=
  fun c => ⟨scalar c, determinant_scalar c⟩

/-- The full determinant-one identity-form isometry group has order 25920. -/
public theorem card_standardSU : Nat.card StandardSU = 25920 := by
  have h := determinant.ker.card_mul_index
  rw [Subgroup.index_ker, determinant.range_eq_top.mpr determinant_surjective,
    Subgroup.card_top, Nat.card_units, standard_field_card,
    ← Nat.card_congr specialEquivKernel.toEquiv, Counting.card_unitary_four] at h
  omega

/-- The exact upper-bound premise of the concrete unitary–symplectic comparison. -/
public theorem card_standardSU_le : Nat.card StandardSU ≤ 25920 :=
  card_standardSU.le

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.UnitaryOrder
