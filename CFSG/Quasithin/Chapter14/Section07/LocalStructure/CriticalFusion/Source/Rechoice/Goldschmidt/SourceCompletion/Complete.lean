module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.GoldschmidtSize.Complete
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion.FullSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.Complete

/-!
# The original critical path with the Gol80 inputs discharged

The proved universal vertex-size bound and complete marked F.6 classification
supply both amalgam premises in the original Chapter 14 quotient comparison.
The actual bang and plus quotients, parabolic marking, and point-generated
module retain their source definitions. Independent earlier structural,
uniqueness, Thompson, faithful-module, and B.5 inputs remain explicit.

Source: Goldschmidt (1980), Theorem A; Aschbacher--Smith F.6.18 and 14.7.70,
printed pp.309--310 and 1074--1075.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion.FullSource
open Subgroup Representation Chapter12.Section08
open QuotientComparison QuotientComparison.Alternatives
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
  (thompson : ThompsonWitness.EarlierThompsonNormality.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
include structural uniqueness thompson faithful b5

/-- The core comparison and actual parabolic marking with both Goldschmidt
premises discharged. -/
theorem core_and_marking_complete (geometry : Geometry d c)
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    CoreFacts c ∧
      pCore 2 (I c) = centralizer ((VI c).subgroupOf (I c) : Set (I c)) ∧
      pPrimeCore 3 (I c) = pCore 2 (I c) ∧ Nonempty (ParabolicMarking c) :=
  core_and_marking d c structural uniqueness thompson faithful b5
    (fun _ _ _ _ _ h hcore => h.card_le_384 hcore)
    FSource.sourceClassification_knownSimple_complete geometry mark hcomm

/-- The actual point-generated module has rank three with no remaining
Goldschmidt size or marked-recognition premise. -/
theorem primeRank_VI_complete (geometry : Geometry d c)
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) : primeRank 2 (VI c) = 3 := by
  obtain ⟨core, _, _, ⟨parabolics⟩⟩ := core_and_marking_complete d c
    structural uniqueness thompson faithful b5 geometry mark hcomm
  exact PointModule.primeRank_VI d c core parabolics geometry

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion.FullSource
