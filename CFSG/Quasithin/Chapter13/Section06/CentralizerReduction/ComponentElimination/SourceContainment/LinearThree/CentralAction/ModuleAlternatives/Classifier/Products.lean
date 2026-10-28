module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Cases
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products.Selection
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products.NaturalSections
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products.DoubledSplitting
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products.HyperplaneModules

/-!
# Product branches of the PSL₃(2) component classifier

The actual normal PSL₃(2) component is one of the original product factors.
Selection retains the multiplication inclusions, both quotient images and
the complete opposite-factor row. Exhausting the selected binary rows gives
the natural component-fixed quotient, including the exceptional four-space
case, or the whole doubled moved space under one actor equivalence.

Only the doubled quotient row needs the full earlier B.5.1 implication and
the universal extraction from its full conclusion. Its splitting proof
establishes every hypothesis on the actual restricted action. These two
authorized earlier inputs remain explicit for the parent classifier to
discharge; no selected factor or local module witness is assumed here.

The reexported `hyperplane_moduleCase` handles B.5.6(5) without any earlier
classification input, exhausting both factors and all allowed multiplicities.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.1,
printed pp.99–103, B.5.6(3),(5), p.105, and 13.6.20, p.931 (PDF p.948).
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products
open ChapterB.SourceInduction
universe u v

/-- Recover the two component module alternatives from the full B.5.6(3)
product. The factor and its binary row are selected from the source data;
the doubled case identifies the moved space itself, not merely its image. -/
theorem twoFactor_moduleCase {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D} [C.Normal]
    {𝒦 : GroupClass.{u}}
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} 𝒦)
    (rows : QuasisimpleRowExtraction.{u,v})
    (hyp : FFHypothesis 𝒦 ρ) (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SourceTwoFactorCase ρ) : LinearThreeModuleCase ρ C := by
  obtain ⟨selected⟩ := select_twoFactor e c
  cases selected.componentCase with
  | natural hm a => exact NaturalSections.natural e selected hm a
  | doubled hm a => exact DoubledSplitting.selected_doubled earlier rows hyp e selected hm a
  | exceptional hm extension => exact NaturalSections.exceptional e selected hm extension

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products
