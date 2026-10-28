module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.ReciprocalSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ActorPlacement

/-!
# The Rudvalis source endpoint with critical placement constructed

The actual path gives Uα≤Q≤R₁. Consequently the EarlierImages record used
throughout 14.7.66–75 is constructed from just its two genuine earlier
quotient facts: Q*=R₁* and the relative Sylow statement in K*. All orbit,
critical-length, original and reciprocal placement and reciprocal parity
premises are discharged on the same source path.

The independent rank selection, 14.7.68–69 and earlier global source
classifications remain explicit and are not asserted by this theorem.
Source: Aschbacher–Smith 14.7.1, 14.7.66–75 and J.1.1.
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

/-- The original source conclusion with the critical image placement constructed. -/
theorem source_rudvalis_of_source_images
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (himage : star F (Q T L) = star F (F.Ri L 1))
    (hsylow : Chapter1.IsSylowIn 2 (star F (F.Ri L 1)) (star F (K F)))
    (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (earlier1332 : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) : Nonempty (G≃*Rudvalis.Model) := by
  exact source_rudvalis_of_reciprocal_source d c structural faithful amalgams sourceF hA hC
    (d.source_earlierImages structural c himage hsylow) selection h69 earlier1332 h68 hcentralizer68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
