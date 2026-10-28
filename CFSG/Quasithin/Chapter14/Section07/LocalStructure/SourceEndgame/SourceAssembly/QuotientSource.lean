module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.ImageSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.StarSylow
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CoreProduct

/-!
# The source Rudvalis endpoint with all critical-image inputs discharged

The original natural action proves QQ_H=R₁, so the literal star quotient
has Q*=R₁*. The existing marked parabolic action proves that R₁* is
Sylow in K*. Combined with the critical-path placement, these construct
every field of EarlierImages on the original selected path. The genuine
13.3.2 module classification was already required by the final consumer;
no new premise is added.

Rank selection, 14.7.68–69 and independent earlier global classifications
remain explicit. Source: Aschbacher–Smith 14.7.4, 14.7.66–75 and J.1.1.
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

/-- The original source conclusion with all earlier-image fields constructed. -/
theorem source_rudvalis_of_source_quotients
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (earlier1332 : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) : Nonempty (G≃*Rudvalis.Model) := by
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S K hK
    exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC hA hC hX S hK
  have himage := (d.source_core_product_of_source1332 structural uniqueness earlier1332).2
  exact source_rudvalis_of_source_images d c structural faithful amalgams sourceF hA hC
    himage (d.source_Ri_star_sylow structural) selection h69 earlier1332 h68 hcentralizer68


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
