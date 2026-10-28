module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.PlaneMovementAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.At
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt.Source

/-!
# Original alternating-five components contain the point

An outside component is first placed in the full point stabilizer, retaining
its actual carrier and core quotient. The original fixed-module source forces
plane movement. The mixed completion then has zero two-core by the actual
overcomponent argument, but its literal original section has rank at least
eight, forcing a nonzero two-core by the Sylow order comparison.
Source: Aschbacher–Smith 14.7.45–46, printed pp.1062–1063.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment
open Chapter12.Section08 CriticalFusion.Source
open Chapter12.Section02 Chapter13.Section03.SourceCompletion
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Every actual original alternating-five component contains the point.
All movement, normality, full-point placement and section-rank data are derived
from the original hypotheses and the earlier fixed-module source. -/
theorem local_alternating_five_component_contains_point_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (fixed : OriginalFixedModule1332At T L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) :
    F.Li L 1 ≤ C.map I.subtype := by
  by_contra hout
  have hm := PlaneMovementAt.original_plane_moved_of_fixed_module_source_at
    d h hab structural previous faithful earlier fixed
  let K := C.map I.subtype
  have hKH : K ≤ F.H := (map_subtype_le C).trans hI.2.1
  let D := K.subgroupOf F.H
  have hD := OvercomponentsAt.outside_five_is_full_point_component_at
    d h hab structural previous faithful earlier I hI C hC eC hout
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  let : D.Normal := local_cComponent_normal_at d h hab structural previous
    faithful earlier F.H K hH hKH hD
  let eKC : K ≃* C := (C.equivMapOfInjective I.subtype I.subtype_injective).symm
  let eDC : D ≃* C := (subgroupOfEquivOfLe hKH).trans eKC
  let eD : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ eDC (pCore_map_iso 2 eDC)).trans eC
  have hmap : D.map F.H.subtype = K := map_subgroupOf_eq_of_le hKH
  have houtD : ¬ F.Li L 1 ≤ D.map F.H.subtype := by
    rw [hmap]
    exact hout
  obtain ⟨hU, a, hdim⟩ := OutsideLinearTwoSourceAt.local_alternating_five_rank_ge_eight_at
    d h hab structural previous faithful earlier F.H hH D hD houtD eD
  let := hU
  have hne := At.original_mixed_core_ne_bot_of_section_rank_of_plane_moved
    d h hab structural previous faithful earlier D eD houtD hm
    (a.representation.comp (QuotientGroup.mk' (pCore 2 F.H)))
    (AlternatingSevenSource.localQuotientSection a) hdim
  exact hne (OvercomponentsAt.full_point_component_mixed_core_eq_bot_of_plane_moved_at
    d h structural previous faithful D hD hm)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment
