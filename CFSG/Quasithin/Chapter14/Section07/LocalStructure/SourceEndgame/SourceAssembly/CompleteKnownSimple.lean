module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.KnownSimpleSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.GoldschmidtSize.Complete
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.Complete

/-!
# The Rudvalis endpoint with the numerical Goldschmidt and F.6 inputs closed

The universal vertex bound from Gol80 and the complete corrected F.6 source
classification are instantiated at the literal source endpoint. The remaining
critical-path, faithful-action, and earlier Chapter 13 inputs stay explicit.
This is the narrow adapter used by the Theorem D assembly.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt
open CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open SteinbergRecognition SteinbergRecognition.ModuleRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
include structural faithful

/-- The literal Rudvalis endpoint with the two independent Goldschmidt inputs
instantiated by their completed source theorems. -/
theorem source_rudvalis_of_complete_goldschmidt
    (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (earlier1332 : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    Nonempty (G ≃* Rudvalis.Model) := by
  exact source_rudvalis_of_known_simple_classification d c structural faithful
    (fun _ _ _ _ _ h hcore => h.card_le_384 hcore)
    FSource.sourceClassification_knownSimple_complete selection h69 earlier1332 h68
    hcentralizer68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
