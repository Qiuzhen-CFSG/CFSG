module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Reduction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Statements

/-!
# Output specifications for the remaining 11.4.2 model sieve

The carriers below are the actual component images in KzT/C_KzT(VK), with
the field size of the original chosen module. They specify the output of
the still-needed B.4/B.5 sieve, and the inputs of the two independent terminal
arguments. No model recognition or terminal exclusion is claimed here.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The three nonalternating survivors on the literal action image. -/
def RankTwoModel : Prop :=
  Source.IsSL ((component E).map (projection E)) 3 (2 ^ E.input.field.degree) ∨
  Source.IsSp ((component E).map (projection E)) 2 (2 ^ E.input.field.degree) ∨
  ClassificationModels.IsG2At ((component E).map (projection E)) (2 ^ E.input.field.degree)

/-- The exceptional actual A7 image, at the original field size four. -/
def AlternatingSevenModel : Prop :=
  E.input.field.degree = 2 ∧
  Chapter1.Section02.LocalModels.IsAlternating ((component E).map (projection E)) 7

/-- The exact group list still to be deduced from the full 11.1.1 alternatives. -/
def SurvivingModels : Prop := RankTwoModel E ∨ AlternatingSevenModel E

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple
