module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource.SourceExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.SelectedSource

/-!
# Original linear-three row exclusion from the earlier module source

The original fixed-module clause of 13.3.2 supplies actual point-core
movement. The source component has its original point inclusion and
Sylow supplement, so the established small-row argument now applies
without a supplied commutator or movement premise.

The fixed-module source remains explicit. It is independent of the
earlier faithful quotient list and of the later Data construction.
Source: Aschbacher--Smith 14.5.21(2), 14.7.48--49, printed pp.1019,1064.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section03.SourceCompletion
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The literal original SL₃(2) row is impossible once the genuine earlier
fixed-module theorem is supplied. All local movement is constructed. -/
theorem source_14_7_49_linear_three_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (fixed : OriginalFixedModule1332At T L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hc := original_core_commutator_eq_point_of_fixed_module_source_at
    d h hab structural previous faithful earlier source47 fixed
  have hgen := (local_component_eq_residual_at d h hab structural previous faithful
    earlier source47 I hI C hC).2.1
  exact (InnerLinearExclusion.Guarded.local_relative_component_small_inner_rows
    h hab structural previous faithful source47 hc I hI C hC
    (source47 I hI C hC).1 hgen.symm).1

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource
