module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.GoldschmidtSize
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion.FullSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceCutAssembly

/-!
# The Gol80 source cuts in the original Chapter 14 critical path

The four geometric and marked-recognition cuts now supply both the universal
vertex-size bound and the corrected F.6 classification. This discharges the
literal `amalgams` parameter in `FullSource`, retaining the original bang and
plus quotients, parabolic marking, and point-generated module. The independent
Chapter 12 structural and uniqueness theorems, Thompson normality, faithful
module classification, and B.5 classification remain explicit. Their source
owners, recorded in `SourceCompletion`, are `qt-12-02`,
`qt-1-02-adequate-assembly`, `qt-14-03-prelim`, and
`qt-b05-general-classification`, respectively.

Source: Goldschmidt (1980), Theorem A and Sections 3--6; Aschbacher--Smith,
F.6.18 and 14.7.70, printed pp.309--310 and 1074--1075. Discharge of the four
source cuts belongs to the `qt-goldschmidt-f6` marked-amalgam assembly.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion.FullSource
open Subgroup Representation Chapter12.Section08
open QuotientComparison QuotientComparison.Alternatives
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open ChapterF.SourceAssembly.Goldschmidt
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
  (thompson : ThompsonWitness.EarlierThompsonNormality.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
  (labels : CanonicalLabelsInput.{u}) (radius : CanonicalRadiusInput.{u})
  (two : RadiusTwoMarkedInput.{u}) (three : RadiusThreeMarkedInput.{u})
include structural uniqueness thompson faithful b5 labels radius two three

/-- The literal size and F.6 premises of the original quotient recognition
are both discharged by the same four independent source cuts. -/
theorem core_and_marking_of_source_cuts (geometry : Geometry d c)
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    CoreFacts c ∧
      pCore 2 (I c) = centralizer ((VI c).subgroupOf (I c) : Set (I c)) ∧
      pPrimeCore 3 (I c) = pCore 2 (I c) ∧ Nonempty (ParabolicMarking c) :=
  core_and_marking d c structural uniqueness thompson faithful b5
    (fun _ _ _ _ _ h hcore =>
      h.card_le_384_of_source_cuts labels radius two three hcore)
    (FSource.sourceClassification_knownSimple_of_source_cuts labels radius two three)
    geometry mark hcomm

/-- The actual point-generated module has rank three, with both Gol80
parameters replaced by the four source cuts and no numerical premise. -/
theorem primeRank_VI_of_source_cuts (geometry : Geometry d c)
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) : primeRank 2 (VI c) = 3 := by
  obtain ⟨core, _, _, ⟨parabolics⟩⟩ := core_and_marking_of_source_cuts d c
    structural uniqueness thompson faithful b5 labels radius two three geometry mark hcomm
  exact PointModule.primeRank_VI d c core parabolics geometry

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion.FullSource
