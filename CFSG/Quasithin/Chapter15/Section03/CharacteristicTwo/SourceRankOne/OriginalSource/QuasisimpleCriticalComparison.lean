module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.ComponentGeneration
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.A6WholeCore
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.QuasisimpleCriticalComparison

/-!
# The original source core from the critical comparison

The original source supplies the quasisimple component, its two-group
supplement, and positive critical distance. Consequently the literal far
endpoint comparison implies the whole-core bound in X. This retains central
fixed layers and feeds the existing alternating-six and G₂ core consumers.

The initial-module argument supplies the edge-centralizer condition. The
actual local commutator estimate remains the geometric MS93 (3.3)--(3.6)
obligation; it is not inferred from a natural constituent.
Source: MS93 (3.6), pp.870--872; AS C.1.32 and 15.3.31, pp.136 and 1132.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover
open EightGeometry.NaturalModule.Recognition ChapterC BinaryMS.MS93
namespace QuasisimpleCriticalComparison
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} (s : SourceData KnownSimple.IsKnownSimple d c)

/-- A literal source comparison bounds the whole original graph core in X. -/
theorem core_le_X
    (hC : EdgeCentralizerCondition (d.S.subgroupOf I))
    (z : Vertex (d.S.subgroupOf I))
    (hc : CriticalPair (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) z
      ((G2Holomorph.geometry s).exists_critical _ rfl))
    (hcomm : ⁅Q (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)),Z (d.S.subgroupOf I) z⁆ ≤
      (frattini (Q (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)))).map
        (Q (d.S.subgroupOf I) (alpha (d.S.subgroupOf I))).subtype ⊔
        X (d.S.subgroupOf I) (alpha (d.S.subgroupOf I))) :
    core (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) ≤
      X (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) := by
  let := s.normal
  let e := subgroupOfEquivOfLe (component_le c)
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := c.core_quotient_quasisimple
  let : IsQuasisimple ((c.L.subgroupOf I) ⧸ pCore 2 (c.L.subgroupOf I)) :=
    IsQuasisimple.of_mulEquiv eq.symm
  have hK := LocalData.thompson_component_in c.le_thompson c.component
  have hgen : c.L.subgroupOf I ⊔ d.S.subgroupOf I = ⊤ := by
    rw [←subgroupOf_sup (component_le c)
      ((Chapter1.isSylowIn_iff.mp ⟨s.sylow,s.sylow_eq⟩).2.1),←s.generated,subgroupOf_self]
  have hsmall := MSCentralOrbit.original_frattini_of_critical_comparison
    (c.L.subgroupOf I) (d.S.subgroupOf I) hK (G2Holomorph.edge_two_group s)
    hgen (G2Holomorph.core_le_edge s) (G2Holomorph.geometry s)
    (G2Holomorph.positive_distance s) hC z hc hcomm
  let := hK.perfect
  have hp : IsPPerfect 2 (c.L.subgroupOf I) := by
    intro N hn hq
    let := hn
    let : Group.IsNilpotent ((c.L.subgroupOf I) ⧸ N) := hq.isNilpotent
    exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hcore := MSCentralOrbit.intrinsic_core_of_frattini_small (c.L.subgroupOf I) hp hsmall
  rw [MSCentralOrbit.graphCore_eq_intrinsic (c.L.subgroupOf I) (d.S.subgroupOf I)
      (G2Holomorph.edge_two_group s) (G2Holomorph.core_le_edge s)
      (G2Holomorph.residual_eq_component s)]
  change ((blockU (c.L.subgroupOf I)).map (c.L.subgroupOf I).subtype).map
    (embedM (d.S.subgroupOf I)) ≤ X (d.S.subgroupOf I) (alpha (d.S.subgroupOf I))
  rw [hcore.1,X,
    Q_alpha _ (G2Holomorph.edge_two_group s) (G2Holomorph.core_le_edge s),
    omegaCenter_map _ _ (embedM_injective _)]
  exact map_mono (commutator_le_left _ _)

/-- The original alternating-six consumer now needs only the local comparison
and its full natural moved/fixed model. -/
theorem alternating_false
    (m : Parabolics.RankTwoParabolicMarking d I c.L
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
      Parabolics.symplecticDerivedParabolic)
    (hC : EdgeCentralizerCondition (d.S.subgroupOf I))
    (z : Vertex (d.S.subgroupOf I))
    (hc : CriticalPair (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) z
      ((G2Holomorph.geometry s).exists_critical _ rfl))
    (hcomm : ⁅Q (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)),Z (d.S.subgroupOf I) z⁆ ≤
      (frattini (Q (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)))).map
        (Q (d.S.subgroupOf I) (alpha (d.S.subgroupOf I))).subtype ⊔
        X (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)))
    (model : BlockModuleModel c.L (CentralCover.BlockModels.multiplicativeAction
      CentralCover.BlockModels.Alternating.action)) : False :=
  source_alternating_false_of_holomorph_core_le_X s m (core_le_X s hC z hc hcomm) model

end QuasisimpleCriticalComparison
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
