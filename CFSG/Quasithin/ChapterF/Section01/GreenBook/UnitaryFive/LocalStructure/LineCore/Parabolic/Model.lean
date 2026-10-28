module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore.Parameters
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Split

/-!
# Shared matrix subgroups for the parameter-four line parabolic

These names specialize the faithful radical and Levi embeddings to the source
model without altering its field, form, flag, or residual. The middle form is
definitionally the model's existing local unitary form. Both the full parabolic
calculation and the commutator calculation can import this module independently.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.11--12(7), printed pp.262--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive.LineCore
open Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
variable (M : Model 4)

/-- The concrete coordinate semidirect product with the model's actual SU₃. -/
abbrev LineRadicalLevi := RadicalLevi M.form

/-- The faithful projective embedding of the radical coordinates. -/
abbrev lineRadicalEmbedding : M.LineRadicalCoordinates →* M.leftParabolic :=
  toParabolic M.form M.matrix

/-- The actual unipotent matrix subgroup; its full-parabolic normality is still to be proved. -/
abbrev lineUnipotent : Subgroup M.leftParabolic := projectiveUnipotent M.form M.matrix

/-- The special-unitary block embedding with the same field and involution. -/
abbrev lineLeviEmbedding : M.LocalUnitaryGroup →* M.leftParabolic :=
  leviParabolic M.form M.matrix

/-- Multiplication of the radical and special-unitary block matrices. -/
abbrev lineRadicalLeviMap : M.LineRadicalLevi →* M.leftParabolic :=
  radicalLeviMap M.form M.matrix

/-- The image of the radical and SU₃; its equality with the residual is a separate result. -/
abbrev lineRadicalLeviSubgroup : Subgroup M.leftParabolic :=
  radicalLeviSubgroup M.form M.matrix

noncomputable abbrev lineRadicalLeviEquiv :
    M.LineRadicalLevi ≃* M.lineRadicalLeviSubgroup := radicalLeviEquiv M.form M.matrix

noncomputable abbrev lineRadicalLeviProjection :
    M.lineRadicalLeviSubgroup →* M.LocalUnitaryGroup := radicalLeviProjection M.form M.matrix

theorem lineRadicalLeviMap_injective : Function.Injective M.lineRadicalLeviMap :=
  radicalLeviMap_injective M.form M.matrix

@[simp] theorem lineRadicalLeviProjection_equiv (x : M.LineRadicalLevi) :
    M.lineRadicalLeviProjection (M.lineRadicalLeviEquiv x) = x.right :=
  radicalLeviProjection_equiv M.form M.matrix x

theorem lineRadicalLeviProjection_ker : M.lineRadicalLeviProjection.ker =
    M.lineUnipotent.subgroupOf M.lineRadicalLeviSubgroup :=
  radicalLeviProjection_ker M.form M.matrix

theorem lineRadicalLeviProjection_surjective : Function.Surjective M.lineRadicalLeviProjection :=
  radicalLeviProjection_surjective M.form M.matrix

noncomputable abbrev lineRadicalLeviProjectionKernelEquiv :
    M.lineRadicalLeviProjection.ker ≃* M.LineRadicalCoordinates :=
  radicalLeviProjectionKernelEquiv M.form M.matrix

theorem lineUnipotent_le_overlap : M.lineUnipotent ≤ M.overlap.subgroupOf M.leftParabolic :=
  projectiveUnipotent_le_overlap M.form M.matrix

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
