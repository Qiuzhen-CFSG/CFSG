module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction.Realization
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction.Kernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.Source

/-!
# The full wreath action of the original linear-three survivor

The original moved factors, in the survivor's prescribed coordinates, identify
the full action of L₀T with SL₃(2) wr C₂. Binary matrix realization and faithful
action give the homomorphism; the original components give the entire base,
and the specified exchanger gives the other coset. The orbit quotient then
forces a two-group kernel. All premises of the original action contract are
discharged here. The separate finite point-stabilizer calculation remains an
explicit input to the diagonal-parabolic consumer.

Source: Aschbacher--Smith 10.1.1(3), 10.2.4 and 10.2.11,
printed pp.741,747,753--754.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- The source action is the full marked wreath action, with a two-group kernel. -/
theorem naturalAction : NaturalActionAt T := by
  intro _ L D s d
  exact ⟨(originalLift s d.fixed_part).actionData⟩

/-- The actual diagonal-parabolic consumer now needs only finite model geometry. -/
theorem diagonalRecognition (hmodel : ModelGeometry) : DiagonalRecognitionAt T :=
  diagonalRecognition_of_action (naturalAction T) hmodel

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction
