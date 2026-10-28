module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.Matrices
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter
/-!
# Marking the split unitary graph automorphism

An explicit orthonormal basis carries the antidiagonal form over the concrete
field of four elements to the identity form used by the exceptional comparison.
Under this basis change, entrywise Frobenius inverts the first matched generator
and fixes the second. These exact equations retain the graph involution when
passing from SU₄(2) to the six-dimensional orthogonal vertex.

Source: Aschbacher–Smith F.5.1(1), printed p.300; GLS3 §2.7.
-/

open Matrix Atlas.Algebra BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
public noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.SplitMarking
abbrev F := GoldenFour
theorem star_involutive : Function.Involutive (starRingAut : F ≃+* F) := fun x => star_star x
abbrev splitForm : HermitianForm 4 F := UnitaryFourFlag.form F starRingAut star_involutive
def basisMatrix : Matrix (Fin 4) (Fin 4) F :=
  !![1,0,0,1; 0,1,1,0; 0,omega,omega^2,0; omega,0,0,omega^2]
def basisInverse : Matrix (Fin 4) (Fin 4) F := star basisMatrix * UnitaryFourFlag.gram F
def basisChange : GL (Fin 4) F :=
  ⟨basisMatrix,basisInverse,by decide +kernel,by decide +kernel⟩
theorem basisChange_form :
    splitForm.conjTranspose basisChange.val * splitForm.form * basisChange.val = 1 := by
  decide +kernel
def splitEquivStandard : splitForm.specialSubgroup ≃* StandardSU :=
  HermitianForm.IdentityGram.specialEquiv splitForm basisChange basisChange_form
theorem splitEquivStandard_val (a : splitForm.specialSubgroup) :
    (splitEquivStandard a).val = basisChange⁻¹ * a.val * basisChange :=
  HermitianForm.IdentityGram.specialEquiv_apply _ _ _ _
theorem splitEquivStandard_symm_val (a : StandardSU) :
    (splitEquivStandard.symm a).val = basisChange * a.val * basisChange⁻¹ :=
  HermitianForm.IdentityGram.specialEquiv_symm_apply _ _ _ _
def graphAut : MulAut StandardSU :=
  (splitEquivStandard.symm.trans (UnitaryFourOuter.matrixAut F starRingAut star_involutive)).trans
    splitEquivStandard
theorem graphAut_splitEquivStandard (a : splitForm.specialSubgroup) :
    graphAut (splitEquivStandard a) =
      splitEquivStandard (UnitaryFourOuter.matrixAut F starRingAut star_involutive a) := by
  change splitEquivStandard (UnitaryFourOuter.matrixAut F starRingAut star_involutive
    (splitEquivStandard.symm (splitEquivStandard a))) = _
  rw [splitEquivStandard.symm_apply_apply]

theorem graphAut_generator_zero : graphAut (unitaryGenerator 0) = (unitaryGenerator 0)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  change (splitEquivStandard
    (UnitaryFourOuter.matrixAut F starRingAut star_involutive
      (splitEquivStandard.symm (unitaryGenerator 0)))).val.val = _
  rw [show ∀ a, (splitEquivStandard a).val = basisChange⁻¹ * a.val * basisChange from
    fun a => HermitianForm.IdentityGram.specialEquiv_apply _ _ _ a]
  have h : (splitEquivStandard.symm (unitaryGenerator 0)).val =
      basisChange * (unitaryGenerator 0).val * basisChange⁻¹ :=
    HermitianForm.IdentityGram.specialEquiv_symm_apply _ _ _ _
  change basisChange.inv *
    ((splitEquivStandard.symm (unitaryGenerator 0)).val.val.map starRingAut) *
      basisChange.val = _
  rw [h]
  decide +kernel
theorem graphAut_generator_one : graphAut (unitaryGenerator 1) = unitaryGenerator 1 := by
  apply Subtype.ext
  apply Units.ext
  change (splitEquivStandard
    (UnitaryFourOuter.matrixAut F starRingAut star_involutive
      (splitEquivStandard.symm (unitaryGenerator 1)))).val.val = _
  rw [show ∀ a, (splitEquivStandard a).val = basisChange⁻¹ * a.val * basisChange from
    fun a => HermitianForm.IdentityGram.specialEquiv_apply _ _ _ a]
  have h : (splitEquivStandard.symm (unitaryGenerator 1)).val =
      basisChange * (unitaryGenerator 1).val * basisChange⁻¹ :=
    HermitianForm.IdentityGram.specialEquiv_symm_apply _ _ _ _
  change basisChange.inv *
    ((splitEquivStandard.symm (unitaryGenerator 1)).val.val.map starRingAut) *
      basisChange.val = _
  rw [h]
  decide +kernel
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.SplitMarking
