module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.PointModel.Geometry
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.Source

/-!
# Completed paired point-model calculation

The independent finite-model contract is discharged with the actual whole
point-stabilizer equivalence. Applying the existing original-action
recognition theorem removes precisely its model-geometry premise. The
original source-action calculation remains the separate input owned by
natural-action recognition; the seed application also retains the independent
intrinsic wreath-residual input. No quotient transport is duplicated here.

Source: Aschbacher--Smith 10.2.4 and 10.2.11, pp.747,753--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.PointModel

/-- The complete finite-model calculation, with no ambient source hypotheses. -/
theorem modelGeometry : ModelGeometry := by
  intro v hv
  exact ⟨pointStabilizer_isCoatom v hv, ⟨pointStabilizerEquivSymmetricWreath v hv⟩⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The actual source consumer now needs only the original action calculation. -/
theorem diagonalRecognition_of_naturalAction (hsource : NaturalActionAt T) :
    DiagonalRecognitionAt T :=
  diagonalRecognition_of_action hsource modelGeometry

/-- The literal seed consumer has no remaining finite point-model premise. -/
theorem parabolicSeed_of_naturalAction (hsource : NaturalActionAt T)
    (hwreath : WreathResidualAt T) : ParabolicSeedAt T :=
  parabolicSeed_of_action hsource modelGeometry hwreath

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.PointModel
