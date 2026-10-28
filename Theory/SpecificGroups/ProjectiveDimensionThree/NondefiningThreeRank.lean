module

public import Theory.SpecificGroups.ProjectiveDimensionThree.NondefiningThreeRank.Commuting
public import Theory.SpecificGroups.ProjectiveDimensionThree.NondefiningThreeRank.Noncommuting
public import Theory.GroupTheory.QuasithinBasic
public import BenderSuzuki.MatrixGroups.Unitary

/-!
# The nondefining three-rank in projective dimension three

Every elementary abelian three-subgroup of PGL₃ over a finite field of
characteristic different from three has order at most nine. For commuting
matrix lifts, two character ratios separate projective classes. For
noncommuting lifts, two scalar commutation factors do so, including the
extraspecial three-group possibility. Together these give three-rank at
most two in PGL₃ and its actual PSL₃ and projective special unitary subgroups.
The unitary bound applies to every nondegenerate Hermitian form.

The conditional assembly interfaces are retained, and the unconditional
theorems discharge their noncommuting premise using the matrix proof.
The source needs this bound away from defining characteristic in the
central-cover argument of Remark A.2.14.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.2.17 and Remark A.2.14, printed pp.37–39.
-/

public section

namespace Matrix.ProjectiveDimensionThree
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups

variable {F : Type*} [Field F] [Finite F]

private instance finite_pgl : Finite PGL(3,F) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

section Conditional

variable (h3 : (3 : F) ≠ 0)
  (hnoncommuting : ∀ H : Subgroup (GL (Fin 3) F),
    IsMulCommutative (H.map ProjGenLinGroup.mk) → ¬ IsMulCommutative H →
      Nat.card (H.map ProjGenLinGroup.mk) ≤ 3 ^ 2)

include h3 hnoncommuting

/-- The two matrix-lift branches imply the elementary-rank bound in actual PGL₃.
The noncommuting branch remains an explicit premise. -/
theorem pgl_primeRank_three_le_two_of_noncommuting_bound : primeRank 3 PGL(3,F) ≤ 2 := by
  apply (primeRank_le_iff_elementary_card_le PGL(3,F)).mpr
  intro A hA
  let := hA
  by_cases hcomm : IsMulCommutative (matrixLift A)
  · let := hcomm
    exact elementary_card_le_nine_of_commuting_lift h3 A
  · have heq : (matrixLift A).map ProjGenLinGroup.mk = A :=
      Subgroup.map_comap_eq_self_of_surjective ProjGenLinGroup.mk_surjective A
    have hproj : IsMulCommutative ((matrixLift A).map ProjGenLinGroup.mk) :=
      heq.symm ▸ hA.toIsMulCommutative
    simpa only [heq] using hnoncommuting (matrixLift A) hproj hcomm

/-- The actual central quotient PSL₃ inherits the PGL₃ bound. -/
theorem psl_primeRank_three_le_two_of_noncommuting_bound : primeRank 3 PSL(3,F) ≤ 2 :=
  (Theory.GroupTheory.primeRank_le_of_injective 3 ProjectiveSpecialLinearGroup.toPGL
    ProjectiveSpecialLinearGroup.toPGL_injective).trans
      (pgl_primeRank_three_le_two_of_noncommuting_bound h3 hnoncommuting)

/-- The actual projective special unitary image inherits the same bound for
any nondegenerate Hermitian form. -/
theorem psu_primeRank_three_le_two_of_noncommuting_bound (J : HermitianForm 3 F) :
    primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 2 :=
  (Theory.GroupTheory.primeRank_le_of_injective 3
    (ProjectiveSpecialUnitaryMatrixGroup J).subtype Subtype.val_injective).trans
      (pgl_primeRank_three_le_two_of_noncommuting_bound h3 hnoncommuting)

end Conditional

/-- The ordinary three-rank of the actual PGL₃ is at most two away from
characteristic three, whether its elementary subgroups have commuting lifts or not. -/
theorem pgl_primeRank_three_le_two (h3 : (3 : F) ≠ 0) : primeRank 3 PGL(3,F) ≤ 2 :=
  pgl_primeRank_three_le_two_of_noncommuting_bound h3
    (card_projective_image_le_nine_of_noncommuting h3)

/-- The actual PSL₃ central quotient has ordinary three-rank at most two
away from characteristic three. -/
theorem psl_primeRank_three_le_two (h3 : (3 : F) ≠ 0) : primeRank 3 PSL(3,F) ≤ 2 :=
  (Theory.GroupTheory.primeRank_le_of_injective 3 ProjectiveSpecialLinearGroup.toPGL
    ProjectiveSpecialLinearGroup.toPGL_injective).trans (pgl_primeRank_three_le_two h3)

/-- For any nondegenerate Hermitian form in dimension three, its actual
projective special unitary image has three-rank at most two in nondefining characteristic. -/
theorem psu_primeRank_three_le_two (h3 : (3 : F) ≠ 0) (J : HermitianForm 3 F) :
    primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 2 :=
  (Theory.GroupTheory.primeRank_le_of_injective 3
    (ProjectiveSpecialUnitaryMatrixGroup J).subtype Subtype.val_injective).trans
      (pgl_primeRank_three_le_two h3)

end Matrix.ProjectiveDimensionThree
