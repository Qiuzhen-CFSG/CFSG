module

public import BenderSuzuki.MatrixGroups.Unitary

/-!
# The natural embedding of projective SU₃ in projective SL₃

Both matrix groups map to the same projective general linear group. Every
special unitary matrix has determinant one, so its projective image lies in
the image of PSL₃. The injective PSL₃-to-PGL₃ map therefore gives an actual
embedding of the projective special unitary group, for every Hermitian form.

This compares the projective image definition of PSU with the central
quotient definition of PSL, without identifying groups by their orders.
It is used for the PSU₃(4) centralizer inspection in Aschbacher–Smith,
combined manuscript (1 March 2004), E.6.23, printed p.254 (PDF p.265).
-/

public section

open Subgroup
open scoped MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm

/-- The inclusion of the actual projective special unitary image into PSL₃. -/
noncomputable def projectiveLinearEmbedding
    {F : Type*} [Field F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) :
    BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J →* PSL(3,F) := by
  let f := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 3) (R := F)
  let e := MonoidHom.ofInjective (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 3) (R := F))
  have hle : J.specialSubgroup.map Matrix.ProjGenLinGroup.mk ≤ f.range := by
    rintro x ⟨g, hg, rfl⟩
    let a : SL(3,F) := ⟨g.val, congrArg Units.val hg.2⟩
    refine ⟨QuotientGroup.mk' (center SL(3,F)) a, ?_⟩
    change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL a) =
      Matrix.ProjGenLinGroup.mk g
    exact congrArg Matrix.ProjGenLinGroup.mk (Units.ext rfl)
  exact e.symm.toMonoidHom.comp (inclusion hle)

/-- The inclusion remains faithful after taking both projective quotients. -/
theorem projectiveLinearEmbedding_injective
    {F : Type*} [Field F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) :
    Function.Injective (projectiveLinearEmbedding J) :=
  (MonoidHom.ofInjective (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 3) (R := F))).symm.injective.comp
    (inclusion_injective _)

end BenderSuzuki.MatrixGroups.HermitianForm
