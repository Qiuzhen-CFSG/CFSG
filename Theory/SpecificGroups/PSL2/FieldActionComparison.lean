module

public import GorensteinWalter.ProjectiveSemilinear
public import Theory.SpecificGroups.PSL2.OuterSolvable.Actions

/-!
# Comparing the two literal projective field actions

Both definitions descend entrywise coefficient application on SL2 through
its center. This identifies the semilinear action used in recognition with
the action carried by the final quasithin field-extension record.
-/

public section
open scoped MatrixGroups
namespace Theory.PSL2

theorem projectiveFieldAutHom_eq_psl2FieldAut
    {F : Type*} [Field F] (σ : F ≃+* F) :
    OuterSolvable.projectiveFieldAutHom σ = GorensteinWalter.psl2FieldAut F σ := by
  ext x
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) x
  rw [GorensteinWalter.psl2FieldAut_apply, GorensteinWalter.psl2RingEquiv_mk]
  exact OuterSolvable.projectiveFieldAutHom_apply_quotientMap σ A

end Theory.PSL2
