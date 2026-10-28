module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo

/-!
# Source alternative comparison for 14.7.70

The checked preparation proves the normal-S₃ obstruction in the actual
 plus quotient, excludes the collapsed F.6.11 case and F.6.18 row (1),
 and applies the complete F.6.18 implication with full KnownSimple SQTK.

Final assembly of BangRecognition remains here. The independent row-(2)
 elimination and rows-(3)–(13) comparison must still supply the actual
 bang equivalence and a subnormal PSL₃(2) inside the original plus quotient.
 Those are separate outputs; this module does not identify the two ambient
 quotients or assume either recognition conclusion.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
 Lemma 14.7.70, printed pp.1074–1075 (PDF pp.1091–1092).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives
open Subgroup
open Chapter12.Section08
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- The complete 14.7.70 comparison.  F.6.18 leaves only its row-(2)
model or the two actual recognition outputs; the native row-(2) argument
eliminates the former.  Thus the result retains the original bang quotient
equivalence and the original subnormal component in the plus quotient. -/
theorem bangRecognition_of_inputs
    (sourceF : FSource.ClassificationInput KnownSimple.IsKnownSimple.{u})
    (rigidity : ChapterF.Noncyclic.GoldschmidtRigidityInput.{u})
    (centralizers : ChapterF.Noncyclic.SectionCentralizerInput.{u,u})
    (h : Geometry d c) (k : CoreFacts c) (small : SmallSubnormal c) :
    Nonempty (BangRecognition c) := by
  rcases Nonsolvable.classified_bang_comparison c d sourceF h k small with hrow | hr
  · exact (RowTwo.not_rowTwo d c rigidity centralizers h k small hrow).elim
  · exact hr

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives
