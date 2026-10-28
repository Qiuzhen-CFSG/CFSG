module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore.Parameters
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Levi.Structure
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Levi.Orbit
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Levi.Basis

/-!
# The SU₃(4) Levi factor and its marked line stabilizer

For every unitary-five model at parameter four, its actual identity-form
SU₃ matrix group is simple and perfect and has trivial two-core. The
stabilizer of the line `(1,1,0)` has index 65: an explicit trace-one Witt
basis marks this line, and matrix conjugation transports the natural
65-point isotropic orbit. All field, basis and action premises are
discharged from the model's parameters.

Source: Aschbacher--Smith, F.1.11--12(7), printed pp.262--264; Huppert,
*Endliche Gruppen I*, II.10.12--13.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive.LineCore
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
variable (M : Model 4)

instance localUnitaryGroup_isSimple : IsSimpleGroup M.LocalUnitaryGroup :=
  Levi.simple M.localUnitaryForm rfl M.localUnitaryForm_conjugation
    M.local_field_card M.line_fixedField_card

instance localUnitaryGroup_isPerfect : Group.IsPerfect M.LocalUnitaryGroup :=
  Levi.perfect M.localUnitaryForm rfl M.localUnitaryForm_conjugation
    M.local_field_card M.line_fixedField_card

theorem pCore_localUnitaryGroup : pCore 2 M.LocalUnitaryGroup = ⊥ :=
  Levi.twoCore M.localUnitaryForm rfl M.localUnitaryForm_conjugation
    M.local_field_card M.line_fixedField_card

theorem localUnitaryLine_eq_span :
    M.localUnitaryLine = Submodule.span M.F {![1, 1, 0]} := by
  ext v
  change (v 1 = v 0 ∧ v 2 = 0) ↔ v ∈ Submodule.span M.F {![1, 1, 0]}
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [h1, h2]
  · rintro ⟨a, rfl⟩
    simp

theorem localUnitaryLineStabilizer_index : M.localUnitaryLineStabilizer.index = 65 := by
  obtain ⟨c, hc⟩ := M.exists_lineTraceOne
  let J₀ := Source.Unitary.FormTransport.standardForm M.localUnitaryForm
  let C := Levi.lineBasis c
  have hC : M.localUnitaryForm.conjTranspose C.val * M.localUnitaryForm.form * C.val =
      J₀.form := Levi.lineBasis_gram M.localUnitaryForm rfl c hc
  let e := Source.Unitary.FormTransport.specialEquiv M.localUnitaryForm C hC
  have h := Levi.lineStabilizer_index_of_transport M.localUnitaryForm J₀
    M.local_field_card M.line_fixedField_card rfl C e
    (Source.Unitary.FormTransport.specialEquiv_apply M.localUnitaryForm C hC)
  have hf : C.val *ᵥ ![1, 0, 0] = ![1, 1, 0] := Levi.lineBasis_first c
  rw [hf, ← M.localUnitaryLine_eq_span] at h
  exact h
end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
