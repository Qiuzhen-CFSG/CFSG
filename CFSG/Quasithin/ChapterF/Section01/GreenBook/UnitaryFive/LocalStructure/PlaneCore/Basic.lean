module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Setup
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Matrices

/-!
# The concrete plane-unipotent subgroup for the unitary-five model

The explicit unitary matrices embed faithfully into the model's right
parabolic. They form a two-group, and their cardinality equals that of the
Hermitian matrix parameters. This is the shared subgroup interface
for the Levi decomposition and the residual calculation assembled in
`PlaneCore.Assembly`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.12(7), printed pp. 263--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model

open Theory.SpecificGroups.UnitaryFive

variable {q : ℕ} (M : Model q)

/-- The full family of plane-unipotent matrix parameters. -/
abbrev RightUnipotentParameters := PlaneCore.Parameters M.form

/-- The actual subgroup obtained from these matrices in the plane parabolic. -/
def rightUnipotent : Subgroup M.rightParabolic :=
  PlaneCore.projectiveUnipotent M.form M.matrix

/-- The parameter group survives the projective quotient faithfully. -/
noncomputable def rightUnipotentEquiv : M.RightUnipotentParameters ≃* M.rightUnipotent :=
  PlaneCore.parametersEquiv M.form M.matrix

theorem rightUnipotent_isPGroup : IsPGroup 2 M.rightUnipotent :=
  PlaneCore.projectiveUnipotent_isPGroup M.form M.matrix

theorem rightUnipotent_card_eq_parameters :
    Nat.card M.rightUnipotent = Nat.card M.RightUnipotentParameters :=
  PlaneCore.projectiveUnipotent_card M.form M.matrix

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
