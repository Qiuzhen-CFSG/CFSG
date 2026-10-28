module

public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Monomial subgroups of the actual special and projective unitary groups

The special subgroup preserves the union of the punctured coordinate axes
under its natural matrix action. The projective subgroup is its image under
the actual special-to-projective map. With identity Gram matrix these are
the stabilizers of the standard orthogonal decomposition into three lines.

These definitions separate the geometric placement of a subgroup from the
calculation of its prime core. Neither assertion is built into the definitions.

Source: GLS3, proof of Theorem 6.5.3(b), `refs/KGroup/GLS3/chapter6.tex`.
-/

@[expose] public section

open scoped Pointwise
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal.Monomial

variable {E : Type*} [Field E]

/-- The union of the three coordinate axes, with zero removed. -/
def coordinateVectors : Set (Fin 3 → E) :=
  {v | ∃ i : Fin 3, v i ≠ 0 ∧ ∀ j : Fin 3, j ≠ i → v j = 0}

/-- The special-unitary matrices that preserve the three coordinate lines. -/
def special (J : HermitianForm 3 E) : Subgroup J.specialSubgroup :=
  (MulAction.stabilizer (GL (Fin 3) E) (coordinateVectors (E := E))).comap
    J.specialSubgroup.subtype

/-- The image in the actual projective special unitary matrix group. -/
def projective (J : HermitianForm 3 E) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (special J).map J.specialToProjective

theorem single_mem_coordinateVectors (i : Fin 3) {a : E} (ha : a ≠ 0) :
    Pi.single i a ∈ coordinateVectors := by
  refine ⟨i, by simpa using ha, ?_⟩
  intro j hj
  simp [hj]

end BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal.Monomial
