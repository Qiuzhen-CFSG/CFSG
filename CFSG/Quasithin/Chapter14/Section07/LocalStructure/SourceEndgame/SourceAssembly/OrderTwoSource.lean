module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FusionSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.SourceAssembly

/-!
# The original Rudvalis endpoint with critical order proved

The source construction of 14.7.69 supplies the order of the literal
critical star image on the original selected path. Thus the final
14.7.75/J.1.1 consumer needs no critical-order premise. Its genuine earlier
reversed-path and fixed-centralizer implications remain explicit, together
with the independent earlier classification and Goldschmidt inputs.
Source: Aschbacher–Smith 14.7.68–75 and J.1.1.
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

/-- The literal source endpoint with critical order and fusion both constructed. -/
theorem source_rudvalis_of_original_order
    (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
      ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384)
    (sourceF : FSource.SourceClassificationInput KnownSimple.IsKnownSimple.{u})
    (selection : c.RankSelection)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (baumann : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (weakClosure : Theorem14731.{u}) (symmetry : d.EarlierSymmetry)
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    Nonempty (G ≃* Rudvalis.Model) :=
  source_rudvalis_of_original_fusion d c structural faithful amalgams sourceF selection
    (d.order_two_of_original_source structural faithful modules baumann weakClosure
      symmetry hcentralizer68 c selection) modules baumann weakClosure hcentralizer68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
