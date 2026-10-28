module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.SevenModule
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.ShortMovedCard
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.LocalAlternatives.SevenBlock

/-!
# Rudvalis recognition from shortness of the original fixed components

The actual moved star subgroup is now a natural six-space of order 64.
For a short fixed component, the omega-center identity identifies that
subgroup with its intrinsic layer. Thus its block module has order at
most 64, and the original K cannot have the two noncentral binary chief
factors already constructed from the original point commutator. This
supplies the required fixed-component alternatives and their literal
Rudvalis and full D-model applications.

Only shortness of the original component remains in this local branch:
no block type, module size, geometric marking or C.2.7 alternative is an
input. Shortness and the earlier original-source premises remain owned by
qt-d-14775-source; these conditional theorems do not finish 14.7.75.
Source: Aschbacher--Smith C.1.7--11, C.2.7 and14.7.68--75,
pp.123--124,145--147 and1071--1078.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data

theorem fixedComponent_C27_module_bound_of_short (d : Data T L V F W)
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hs : ChapterC.IsShort Lu) : Nat.card (ChapterC.BlockModule Lu) ≤ 64 := by
  have hb := ChapterC.C27Source.blockModule_card_le_star_moved_of_short Lu (d.fixedCore u)
    (d.fixedCore_normalizes_component u h) hs
  rwa [d.fixedComponent_C27_moved_card u h] at hb
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def FixedComponentShortness (d : Data T L V F W) : Prop :=
  ∀ (u : F.U) (Lu : Subgroup G), Nonquasisimple.Case d u Lu → ChapterC.IsShort Lu

theorem fixedComponentAlternatives_of_shortness
    (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (short : FixedComponentShortness d) : FixedComponentAlternatives d := by
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S B hB
    exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
      (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y)) hX S hB
  have hcomm := d.U_core_commutator_eq_point_of_source1332 modules structural uniqueness
  intro u Lu h
  have hs := short u Lu h
  obtain ⟨s,hs0,hs1,hs2⟩ := d.exists_K_two_chief_of_point_commutator hcomm
  have hb := AlternatingBound.count_le_one_of_embedding hs
    (d.KToFixedComponent u h) (inclusion_injective h.larger.le)
    (d.fixedComponent_C27_core_alternatingSeven u h).some d.KCoreA5 (K_twoPerfect F)
    (d.fixedComponent_C27_module_bound_of_short u h hs) s hs0 hs1
  omega

variable (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
  (short : FixedComponentShortness d)
include d structural faithful modules short

theorem source_rudvalis_of_short_fixed_components : Nonempty (G ≃* Rudvalis.Model) :=
  source_rudvalis_of_naturalPointMS_local_alternatives d structural faithful modules
    (fixedComponentAlternatives_of_shortness d structural modules short)

theorem source_theoremDModel_of_short_fixed_components : ClassificationModels.IsTheoremDModel G :=
  source_theoremDModel_of_naturalPointMS_local_alternatives d structural faithful modules
    (fixedComponentAlternatives_of_shortness d structural modules short)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
