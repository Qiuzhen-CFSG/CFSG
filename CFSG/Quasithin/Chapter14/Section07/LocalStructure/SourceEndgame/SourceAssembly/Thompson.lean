module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.EarlierSource
public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource.Consumer

/-!
# Source14.3.9(2) discharges the Thompson input in70–72

Apply the proved universal natural-flag Thompson normality theorem to the
literal Goldschmidt consumer. This preserves all original source actions
and the one critical rechoice, while removing the Thompson implication
from the final rechoice and generation premises.

Source: Aschbacher–Smith,14.3.9(2) and14.7.70–72.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open SteinbergRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
  (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
    ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384)
  (sourceF : FSource.ClassificationInput KnownSimple.IsKnownSimple.{u})
include structural uniqueness faithful b5 amalgams sourceF

/-- The source rechoice and generation with native Thompson normality discharged. -/
theorem rechoice_and_generation
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (hmove : ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G))
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (earlier_conjugacy : ∀ c' : CriticalPath (L := L) F, c'.Zα ≤ V →
      c'.b = 3 ∧ ∃ l ∈ L, c'.Uα = conjugate F.U l)
    (h13 : ∀ n : group F L, SourceGeneration.EarlierThirteen (c.reselect n))
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    Statement c d ∧ SourceGeneration.Conclusion d :=
  rechoice_and_generation_of_earlier_source d c structural uniqueness
    (Chapter14.Section03.ThompsonSource.earlierThompsonNormality structural)
    faithful b5 amalgams sourceF earlier selection h69 hmove h68 hUH heven
    earlier_conjugacy h13 hcentralizer68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
