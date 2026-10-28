module

public import BenderSuzuki.MatrixGroups.Unitary

/-!
# The projective unitary embedding into a projective linear group

SU(J) is a subgroup of SL over the coefficient field. In the concrete model,
PSU(J) is its image in PGL; this image lies in the canonical image of PSL.
The injectivity of PSL → PGL therefore gives an injection PSU(J) → PSL.
This argument compares the actual images and requires no identification of
an abstract quotient by an incorrectly chosen center.

For PSU_n(q) the coefficient field has order q², so the target is PSL_n(q²).
Source: the defining projective matrix constructions for the classical groups.
-/

open BenderSuzuki.MatrixGroups

namespace BenderSuzuki.MatrixGroups.HermitianForm

/-- The actual projective special unitary matrix group embeds in the projective
special linear group over the same coefficient field. -/
public theorem exists_injective_projectiveSpecialLinear
    {n : ℕ} {F : Type*} [Field F] (J : HermitianForm n F) :
    ∃ i : ProjectiveSpecialUnitaryMatrixGroup J →*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) F, Function.Injective i := by
  classical
  let j : Matrix.ProjectiveSpecialLinearGroup (Fin n) F →*
      Matrix.ProjGenLinGroup (Fin n) F := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hle : J.specialSubgroup.map Matrix.ProjGenLinGroup.mk ≤ j.range := by
    rintro _ ⟨A, hA, rfl⟩
    have hdet : A.val.det = 1 := by
      have h := (J.mem_specialSubgroup_iff A).mp hA |>.2
      simpa using congrArg Units.val h
    let s : Matrix.SpecialLinearGroup (Fin n) F := ⟨A.val, hdet⟩
    have hs : Matrix.SpecialLinearGroup.toGL s = A := by
      ext i k
      rfl
    refine ⟨QuotientGroup.mk s, ?_⟩
    change Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk s) = _
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, hs]
  let e := MonoidHom.ofInjective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin n) (R := F))
  let i := e.symm.toMonoidHom.comp (Subgroup.inclusion hle)
  exact ⟨i, e.symm.injective.comp (Subgroup.inclusion_injective hle)⟩

end BenderSuzuki.MatrixGroups.HermitianForm

