module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion.ModuleSeparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceNoncentrality
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FromRechoice

/-!
# Rechoice and generation from the actual earlier plane action

The natural module proves14.7.2(1) internally. The original13.3.14 plane
noncentrality and the exact earlier section kernel give[U,Q_H]=V₁. These
supply every marked-module input to the completed source70 route. Retain
its single selected path and use that same point-commutator witness in
source72, returning both the original70 statement and the generation
conclusions. No separation, marked actor, core action, commutator equality
or local Goldschmidt conclusion remains as an extra premise.

The independent13.3.14 plane action,14.7.13 central/derived spans,
14.7.68/69 conclusions, original path selection/images/conjugacy and
universal classification implications retain their earlier producers.
Source: Aschbacher–Smith,13.3.14,14.7.2(1),14.7.70–72.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt
open CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open SteinbergRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
  (thompson : ThompsonWitness.EarlierThompsonNormality.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
  (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
    ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384)
  (sourceF : FSource.ClassificationInput KnownSimple.IsKnownSimple.{u})
include structural uniqueness thompson faithful b5 amalgams sourceF

/-- The actual70 producer discharges all selected-path generation premises. -/
theorem rechoice_and_generation_of_earlier_source
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
    Statement c d ∧ SourceGeneration.Conclusion d := by
  have separation := Rechoice.SourceCompletion.moduleSeparation d
  have hcomm := d.U_core_commutator_eq_point_of_plane_moved
    (d.sectionCentralizer_of_earlier_setup structural uniqueness) hmove
  let d' := LeftChiefFactors.BorelRefinements.upperRemark d structural
  obtain ⟨n, _, hpoint, hp, hrank, hi, hV, hU₀, hb, hconj⟩ :=
    Rechoice.SourceCompletion.source_rechoice_with_point d c structural uniqueness thompson
      faithful b5 amalgams sourceF earlier selection h69 separation hcomm h68 hUH heven
      earlier_conjugacy
  have hout := generation_of_selected_rechoice d' structural c n earlier separation
    (d'.sectionCentralizer_of_earlier_setup structural uniqueness)
    (LeftChiefFactors.BorelRefinements.upperRemark_upperMarking d structural)
    (Rechoice.SourceCompletion.localActors_of_source d structural)
    h69 hp hrank hi hV hU₀ hb hconj (h13 n) hpoint hcentralizer68
  refine ⟨⟨n, hp, hrank, hi, hV, hU₀, hb, hconj⟩, ?_⟩
  exact ⟨hout.original_commutator, hout.span_central, hout.span_intersection,
    hout.residual_commutator, hout.actor_commutator, hout.span_join, hout.fixed_kernel,
    hout.fixed_span, hout.seed_central, hout.frattini_eq, hout.derived_eq,
    hout.core_commutator, hout.seed_central_in_Q⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
