module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete

/-!
# The actual 14.7.70 witness with B.5 discharged

The unconditional adequate B.5 theorem applies to the faithful original
Thompson action and supplies the small subnormal subgroup in the literal
I/O2(I). The independent earlier setup, Thompson normality and faithful local
classification contracts remain exactly those of the Chapter 14 source.
Only the earlier B.5 premise is discharged here.
Source: Aschbacher--Smith 14.7.70, printed pp.1074--1075.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness
open Chapter12.Section08
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- The genuine higher consumer no longer assumes adequate B.5 classification. -/
theorem smallSubnormal_of_source_classification (h : Geometry d c) (k : CoreFacts c)
    (earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (thompson : EarlierThompsonNormality.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G)) :
    SmallSubnormal c :=
  smallSubnormal d c h k earlier thompson classification
    ChapterB.SourceInduction.adequateClassification_knownSimple

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness
