module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.QuotientSource
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The source Rudvalis endpoint with the full known-simple catalogue

The completed simultaneous Theorems A, B and C instantiate the universal
proper-section inputs of the literal 14.7.75 source consumer. In particular,
the 1.2.7 uniqueness application uses the complete known-simple catalogue.
No carrier-family or model-section parameter remains in this application.

The separate earlier Chapter12/13 setup and faithful module classification,
critical rank/fusion statements, and full Goldschmidt source classification
remain explicit. This is their final original-group consumer, not a proof
of those independent source families.
Source: Aschbacher–Smith A.2.1–3, 1.2.7, 14.7.75 and J.1.1.
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
  (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
    ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384)
  (sourceF : FSource.SourceClassificationInput KnownSimple.IsKnownSimple.{u})
include structural faithful amalgams sourceF

/-- The original14.7.75 conclusion using the proved full A/B/C classification. -/
theorem source_rudvalis_of_known_simple_classification
    (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (earlier1332 : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) : Nonempty (G≃*Rudvalis.Model) := by
  exact source_rudvalis_of_source_quotients d c structural faithful amalgams sourceF
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    selection h69 earlier1332 h68 hcentralizer68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
