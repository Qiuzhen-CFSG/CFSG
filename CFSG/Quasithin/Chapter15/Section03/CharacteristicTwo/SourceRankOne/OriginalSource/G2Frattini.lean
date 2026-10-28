module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.G2InitialModule
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.FrattiniCore
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.MovingSection
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
/-!
# The original G₂ branch from the source Frattini containment

Burnside's Frattini action kernel identifies [O₂(I),L] with the moving part
of Ω₁Z(O₂(I)). The natural initial section then identifies the full intrinsic
block quotient, including its central fixed attachment. Literal transport
back to L supplies all three inputs of the original G₂ terminal.

Only the displayed Frattini containment remains as an earlier MS93 input.
The critical-distance argument and non-Frattini comparison must prove it;
no model or block classification is assumed here.
Source: Meierfrankenfeld–Stellmacher (1993), (3.6), pp.870–872;
Aschbacher–Smith C.1.32 and 15.3.31, pp.136,1132.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover
open EightGeometry.NaturalModule.Recognition ChapterC
open Stellmacher.PushingUp.AmalgamGraph
namespace G2Holomorph
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} (s : SourceData KnownSimple.IsKnownSimple d c)
  (m : Parabolics.RankTwoParabolicMarking d I c.L CentralCover.BlockModels.G2.Actor
      Parabolics.g2DerivedParabolic)
include s m
open BinaryMS.MS93
open CentralCover.BlockModels

variable (hsmall : ⁅pCore 2 I,c.L.subgroupOf I⁆ ≤
  (frattini (pCore 2 I)).map (pCore 2 I).subtype ⊔ omegaCenterIn (pCore 2 I))

include hsmall

omit m hsmall in
private theorem relative_twoPerfect : IsPPerfect 2 (c.L.subgroupOf I) := by
  rw [←residual_eq_component s]
  exact isPPerfect_pResidual 2

omit m in
private theorem intrinsic_moved_eq :
    (blockU (c.L.subgroupOf I)).map (c.L.subgroupOf I).subtype =
      ⁅omegaCenterIn (pCore 2 I),c.L.subgroupOf I⁆ := by
  let := s.normal
  exact (MSCentralOrbit.intrinsic_core_of_frattini_small _ (relative_twoPerfect s) hsmall).1

omit m in
theorem core_le_X_of_frattini_small :
    core (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) ≤
      X (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) := by
  let := s.normal
  rw [core_alpha _ (edge_two_group s) (core_le_edge s) (residual_eq_component s),
    MSCentralOrbit.commutatorCore_eq_intrinsic _ (relative_twoPerfect s)]
  change ((blockU (c.L.subgroupOf I)).map (c.L.subgroupOf I).subtype).map
    (embedM (d.S.subgroupOf I)) ≤ _
  rw [intrinsic_moved_eq s hsmall]
  rw [X,Q_alpha _ (edge_two_group s) (core_le_edge s),
    omegaCenter_map _ _ (embedM_injective _)]
  exact map_mono (commutator_le_left _ _)

theorem natural_block_model_of_frattini_small :
    Nonempty (BlockModuleModel c.L (multiplicativeAction G2.action)) := by
  let := s.normal
  let := quotientComponent_normal s
  obtain ⟨E⟩ := (initial_moved_natural s m).2
  have hm := BlockMovingSection.model_of_moving
    (omegaCenterIn (pCore 2 I)) (c.L.subgroupOf I)
    (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (central_omega_centralizer s m).symm)
    (intrinsic_moved_eq s hsmall)
    (cComponentTwoCoreQuotientEquiv
      (Parabolics.Placement.ModelComparison.component_isCComponent_in d c))
    (fun _ => rfl) (Representation.g2DerivedNatural (ZMod 2)) E
  have hm' := hm.of_mulEquiv (subgroupOfEquivOfLe (component_le c))
  obtain ⟨r,⟨model⟩,hr⟩ := hm'
  have he : r = multiplicativeAction G2.action := by
    ext g v
    apply Multiplicative.toAdd.injective
    exact hr g v
  exact he ▸ ⟨model⟩

/-- The literal original G₂ branch is reduced to the source Frattini-small
commutator containment; all model, elementary and central-core inputs are
constructed from the original source hypotheses. -/
theorem false_of_frattini_small : False := by
  obtain ⟨model⟩ := natural_block_model_of_frattini_small s m hsmall
  exact g2_false_of_core_le_X s m (core_le_X_of_frattini_small s hsmall) model

end G2Holomorph
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
