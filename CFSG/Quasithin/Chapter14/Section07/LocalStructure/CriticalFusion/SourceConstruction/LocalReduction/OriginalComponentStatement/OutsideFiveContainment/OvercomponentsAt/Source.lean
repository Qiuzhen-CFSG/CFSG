module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt.FullPoint
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt.MixedCore

/-!
# The original outside A₅ component in the mixed group

The literal component of any original local I is first proved to be a
component of the full point stabilizer. Its original carrier is retained
when the internally constructed overcomponent and LT uniqueness exclude
the nonzero two-core alternative. The genuine source plane movement is
explicit at this intermediate boundary; no component placement is assumed.
Source: Aschbacher–Smith 14.7.45–46, printed pp.1062–1063.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
open Chapter12.Section08 Chapter12.Section09.NaturalSource CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original arbitrary-local outside A₅ has a zero-core mixed completion
once the original point-core movement from 14.7.4 is available. -/
theorem outside_five_mixed_core_eq_bot_of_plane_moved_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥) :
    pCore 2 (C.map I.subtype ⊔ planeCoreClosure F ⊔ (T : Subgroup G) : Subgroup G) = ⊥ := by
  let K := C.map I.subtype
  have hKH : K ≤ F.H := (map_subtype_le C).trans hI.2.1
  have hc := outside_five_is_full_point_component_at d h hab structural previous faithful
    earlier I hI C hC eC hout
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  let : (K.subgroupOf F.H).Normal := local_cComponent_normal_at d h hab structural previous
    faithful earlier F.H K hH hKH hc
  have hh := full_point_component_mixed_core_eq_bot_of_plane_moved_at
    d h structural previous faithful (K.subgroupOf F.H) hc hm
  have he : (K.subgroupOf F.H).map F.H.subtype = K := map_subgroupOf_eq_of_le hKH
  rw [he] at hh
  exact hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
