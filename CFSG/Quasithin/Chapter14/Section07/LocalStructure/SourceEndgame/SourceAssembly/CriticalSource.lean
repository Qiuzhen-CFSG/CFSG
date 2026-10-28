module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OrbitSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ReciprocalPlacement

/-!
# The original critical-path Rudvalis endpoint

The literal point stabilizer is the original centralizer of z. Its natural
L-action and the geodesic give the distance-three conclusion of F.9.14(3).
The original H-orbit span fixes the terminal vertex by the ball-kernel
argument, supplying the reciprocal placement. Together with the proved
14.7.12–13 orbit and span identities, this removes the critical-length callback from the source 14.7.70–75 application.
The group, path, allowed rechoices, quotient maps and full K-catalogue are
unchanged. The earlier source setup, fusion and local classification inputs
remain explicit for their separate source producers.

Source: Aschbacher–Smith F.9.14(3), 14.7.3(4), and 14.7.70–75.
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

/-- The literal original-source Ru conclusion with critical geometry discharged. -/
theorem source_rudvalis_of_critical_source
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (earlier1332 : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) : Nonempty (G≃*Rudvalis.Model) := by
  exact source_rudvalis_of_source_orbits d c structural faithful amalgams sourceF hA hC
    earlier selection h69 earlier1332 h68 (d.source_reciprocal_placement c) heven
    (fun c' hc => d.critical_length_three c' hc) hcentralizer68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
