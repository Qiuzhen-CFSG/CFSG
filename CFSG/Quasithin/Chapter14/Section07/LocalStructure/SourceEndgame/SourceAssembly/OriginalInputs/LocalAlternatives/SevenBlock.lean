module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.SevenGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.NaturalPointMSDeduction

/-!
# Rudvalis recognition after the fixed-component geometry reduction

Every actual nonquasisimple fixed component now has core quotient A₇ and
the proved transposition geometry. The only remaining local premise is
recognition of its original block module. Either ordinary or exceptional
A₇ blocks bound the original K-chief count by one, contradicting the two
factors supplied by the original commutator identity. This discharges the
local-alternatives input in the actual Rudvalis and full D-model consumers.

Block recognition is an explicit unproved source premise here, retained by
qt-d-14775-source together with final earlier-source discharge. These
conditional exports do not assert the unconditional original14.7.75 theorem.
The original Data, structural, faithful and module hypotheses are preserved.
Source: Aschbacher--Smith C.2.7, pp.145--147, and 14.7.68--75, pp.1071--1078.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def FixedSevenBlockRecognition (d : Data T L V F W) : Prop :=
  ∀ (u : F.U) (Lu : Subgroup G), Nonquasisimple.Case d u Lu →
    Nonquasisimple.SevenGeometry d u Lu →
      ChapterC.IsAlternatingBlock Lu 7 ∨ ChapterC.IsExceptionalA7Block Lu

theorem fixedComponentAlternatives_of_seven_block_recognition
    (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (blocks : FixedSevenBlockRecognition d) : FixedComponentAlternatives d := by
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S B hB
    exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
      (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y)) hX S hB
  have hcomm := d.U_core_commutator_eq_point_of_source1332 modules structural uniqueness
  intro u Lu h
  obtain ⟨geo⟩ := d.fixedComponent_C27_seven_geometry u h
  have block := blocks u Lu h geo
  have short : ChapterC.IsShort Lu := block.elim (fun hb => hb.2.1) (fun hb => hb.1)
  have core := d.fixedComponent_C27_core_alternatingSeven u h
  obtain ⟨s,hs0,hs1,hs⟩ := d.exists_K_two_chief_of_point_commutator hcomm
  have hb := AlternatingBound.count_le_one_of_embedding short
    (d.KToFixedComponent u h) (inclusion_injective h.larger.le)
    core.some d.KCoreA5 (K_twoPerfect F) (AlternatingBound.module_card_le_of_a7 block)
    s hs0 hs1
  omega

variable (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
  (blocks : FixedSevenBlockRecognition d)
include d structural faithful modules blocks

theorem source_rudvalis_of_fixedSeven_block_recognition : Nonempty (G ≃* Rudvalis.Model) :=
  source_rudvalis_of_naturalPointMS_local_alternatives d structural faithful modules
    (fixedComponentAlternatives_of_seven_block_recognition d structural modules blocks)

theorem source_theoremDModel_of_fixedSeven_block_recognition : ClassificationModels.IsTheoremDModel G :=
  source_theoremDModel_of_naturalPointMS_local_alternatives d structural faithful modules
    (fixedComponentAlternatives_of_seven_block_recognition d structural modules blocks)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
