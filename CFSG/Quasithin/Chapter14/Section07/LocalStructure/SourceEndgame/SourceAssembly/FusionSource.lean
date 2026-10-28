module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.KnownSimpleSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.SourceFusion

/-!
# The original Rudvalis endpoint with fusion proved

The original residual normalizer argument supplies 14.7.68(1) on the same
source Data and CriticalPath. This removes the fusion premise from the
known-simple 14.7.75/J.1.1 consumer. Its separate centralizer clause of
14.7.68(2), critical order/rank and Goldschmidt classification inputs remain
explicit; none is inferred from the fusion equality.
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

/-- The literal source endpoint with 14.7.68(1) constructed from earlier theorems. -/
theorem source_rudvalis_of_original_fusion
    (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
      ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384)
    (sourceF : FSource.SourceClassificationInput KnownSimple.IsKnownSimple.{u})
    (selection : c.RankSelection) (h69 : Nat.card (star F c.Uα) = 2)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (baumann : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (weakClosure : Theorem14731.{u})
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    Nonempty (G ≃* Rudvalis.Model) :=
  source_rudvalis_of_known_simple_classification d c structural faithful amalgams sourceF
    selection h69 modules
    (d.fusion_z_of_known_simple_source structural faithful modules baumann weakClosure)
    hcentralizer68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
