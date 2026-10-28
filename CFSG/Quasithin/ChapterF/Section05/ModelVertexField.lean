module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.SplitMarking
import all Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
/-!
# The literal F.5 unitary carrier with its graph marking

Entrywise transport from the source's Galois field to the concrete field of
four elements commutes with Frobenius. The explicit split-to-identity basis
then identifies the source projective base with the standard special unitary
group, and sends its specified graph automorphism to the marked automorphism
used in the exterior comparison. The internal import is used only for the
entrywise equation of the existing coefficient transport.

Source: Aschbacher–Smith F.5.1(1), printed p.300.
-/

open BenderSuzuki.MatrixGroups Matrix
open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
namespace CFSG.Quasithin.ChapterF.Section05
open GreenBook.LieModels
public noncomputable section

def modelFieldEquiv : UnitaryFour.MatrixField 1 ≃+* Atlas.Algebra.GoldenFour := by
  let := Fintype.ofFinite (UnitaryFour.MatrixField 1)
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, UnitaryFour.matrixField_card 1 (by decide),
      Atlas.Algebra.goldenFour_card]
    norm_num)

theorem modelFieldEquiv_conj (x : UnitaryFour.MatrixField 1) :
    modelFieldEquiv (UnitaryFour.fieldConj 1 x) = star (modelFieldEquiv x) := by
  rw [UnitaryFour.fieldConj_apply]
  change modelFieldEquiv (x^2) = standardForm.conj (modelFieldEquiv x)
  rw [standard_conj, map_pow]

def modelMatrixEquivSplit : UnitaryFour.MatrixGroup 1 (Nat.le_refl 1) ≃*
    SplitMarking.splitForm.specialSubgroup :=
  HermitianForm.coefficientSpecialEquiv modelFieldEquiv
    (UnitaryFour.standardForm 1 (Nat.le_refl 1)) SplitMarking.splitForm
    modelFieldEquiv_conj (by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [UnitaryFour.standardForm, UnitaryFourFlag.form, UnitaryFourFlag.gram])

theorem modelMatrixEquivSplit_entry (a : UnitaryFour.MatrixGroup 1 (Nat.le_refl 1))
    (i j : Fin 4) :
    (modelMatrixEquivSplit a).val.val i j = modelFieldEquiv (a.val.val i j) := by rfl

theorem modelMatrixEquivSplit_aut (a : UnitaryFour.MatrixGroup 1 (Nat.le_refl 1)) :
    modelMatrixEquivSplit (UnitaryFour.Extension.matrixAut 1 (Nat.le_refl 1) a) =
      UnitaryFourOuter.matrixAut SplitMarking.F starRingAut SplitMarking.star_involutive
        (modelMatrixEquivSplit a) := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  change modelFieldEquiv (UnitaryFour.fieldConj 1 (a.val.val i j)) =
    star (modelFieldEquiv (a.val.val i j))
  exact modelFieldEquiv_conj _
def modelUnitaryEquivStandard :
    UnitaryFour.ProjectiveGroup 1 (Nat.le_refl 1) ≃* StandardSU :=
  (UnitaryFour.Extension.projectEquiv 1 (Nat.le_refl 1)).symm.trans
    (modelMatrixEquivSplit.trans SplitMarking.splitEquivStandard)

theorem modelUnitaryEquivStandard_graph (a : UnitaryFour.ProjectiveGroup 1 (Nat.le_refl 1)) :
    modelUnitaryEquivStandard (UnitaryFour.Extension.projectiveAut 1 (Nat.le_refl 1) a) =
      SplitMarking.graphAut (modelUnitaryEquivStandard a) := by
  obtain ⟨a,rfl⟩ := (UnitaryFour.Extension.projectEquiv 1 (Nat.le_refl 1)).surjective a
  rw [UnitaryFour.Extension.projectiveAut_project]
  simp only [modelUnitaryEquivStandard, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [SplitMarking.graphAut_splitEquivStandard, modelMatrixEquivSplit_aut]

end
end CFSG.Quasithin.ChapterF.Section05
