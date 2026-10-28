module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete
public import CFSG.Quasithin.ChapterJ.Section01.SourceRecognition

/-!
# The original 14.7.75 endpoint with Rudvalis recognition and B.5 discharged

The completed original Type-Ru theorem identifies the group constructed by the
14.7.70–75 source chain with the concrete Rudvalis carrier. The unconditional
adequate B.5 classification supplies its former B.5 input internally. The
independent earlier Chapter13, critical-choice, fusion and F-source results
retain their exact original maps and hypotheses; no source conclusion is added.

Source: Aschbacher–Smith14.7.75, printed pp.1077–1078, and J.1.1.
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

/-- The actual Ru carrier, retaining only genuine earlier source inputs. -/
theorem source_rudvalis_of_theoremsAC
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (earlier1332 : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (earlier_conjugacy : ∀ c' : CriticalPath (L := L) F, c'.Zα ≤ V →
      c'.b = 3 ∧ ∃ l ∈ L, c'.Uα = conjugate F.U l)
    (h13 : ∀ n : group F L, SourceGeneration.EarlierThirteen (c.reselect n))
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) : Nonempty (G≃*Rudvalis.Model) := by
  apply ChapterJ.theorem_J_1_1
  exact source_typeRu_of_theoremsAC d c structural faithful
    ChapterB.SourceInduction.adequateClassification_knownSimple amalgams sourceF hA hC
    earlier selection h69 earlier1332 h68 hUH heven earlier_conjugacy h13 hcentralizer68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
