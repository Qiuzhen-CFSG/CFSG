module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Decomposition.GlobalOffender
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl

/-!
# Original-source application of the global offender classification

The earlier structural and uniqueness theorems put the original R₁ in Y
as a Sylow subgroup. Applying the global offender theorem on precisely this
subgroup removes the Sylow-placement premise from the component/module
conclusion. The only group classification input is the genuine earlier
faithful classification; the full B.5 theorem is instantiated internally.

Source: Aschbacher–Smith, 14.7.67(4), printed pp.1070–1071.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ResidualNormalizer
open Chapter14.Section04.LargerDimension.LocalAction.Components
open ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- B.5 on the actual residual action, with Sylow placement supplied by
the original 12.2.2 and 1.2.7 source implications. -/
theorem Data.residual_global_component_classification_of_source
    (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    let hs := (d.residual_intersections structural uniqueness).2.2.2
    let := (d.residualSpan_reduced hs).elementary
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion (d.residualGlobalAction hs)
      (d.residualGlobalComponent hs B)) :=
  d.residual_global_component_classification earlier
    (d.residual_intersections structural uniqueness).2.2.2 hB

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
