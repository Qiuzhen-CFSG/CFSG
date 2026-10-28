module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFourParabolicCardinality
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourRadicalCentralizers
public import Theory.PGroupCore

/-!
# Self-centralizing two-cores in the full PSU₅(4) parabolics

The concrete line and plane unipotent subgroups are normal two-subgroups
of their full projective parabolics, so each lies in the respective two-core.
An element centralizing that two-core centralizes the unipotent subgroup.
The matrix centralizer calculations place it back in that subgroup, hence
in the full parabolic's two-core. No equality of the radical and two-core
or assertion about solvable residuals is needed.

Source: the defining-characteristic parabolic calculation supporting
Aschbacher–Smith, Theorem 0.1.2(1), printed p.4 (Theorem 0.1.1(1), p.482),
and the unitary-five groups of F.1.12(7), printed pp.263–264.
-/

namespace Theory.SpecificGroups.UnitaryFive

open BenderSuzuki.MatrixGroups

variable {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 5 F)

/-- The intrinsic two-core of the full projective line parabolic is self-centralizing. -/
public theorem lineParabolic_centralizer_twoCore_le (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    Subgroup.centralizer (pCore 2 (lineParabolic J) : Set (lineParabolic J)) ≤
      pCore 2 (lineParabolic J) := by
  have hU : LineCore.Parabolic.projectiveUnipotent J hJ ≤ pCore 2 (lineParabolic J) :=
    le_sSup ⟨line_projectiveUnipotent_normal_four J hcard hconj hJ,
      LineCore.Parabolic.projectiveUnipotent_isPGroup J hJ⟩
  exact (Subgroup.centralizer_le hU).trans
    ((RadicalCentralizers.line_centralizer_le J hJ hconj hcard).trans hU)

/-- The intrinsic two-core of the full projective plane parabolic is self-centralizing. -/
public theorem planeParabolic_centralizer_twoCore_le (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    Subgroup.centralizer (pCore 2 (planeParabolic J) : Set (planeParabolic J)) ≤
      pCore 2 (planeParabolic J) := by
  have hU : PlaneCore.projectiveUnipotent J hJ ≤ pCore 2 (planeParabolic J) :=
    le_sSup ⟨PlaneCore.projectiveUnipotent_normal J hJ,
      PlaneCore.projectiveUnipotent_isPGroup J hJ⟩
  exact (Subgroup.centralizer_le hU).trans
    ((RadicalCentralizers.plane_centralizer_le J hJ hconj hcard).trans hU)

end Theory.SpecificGroups.UnitaryFive
