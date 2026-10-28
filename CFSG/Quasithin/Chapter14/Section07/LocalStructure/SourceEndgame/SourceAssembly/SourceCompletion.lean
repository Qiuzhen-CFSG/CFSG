module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FromRechoice

/-!
# The original rechoice feeds source generation

Construct the unique selected path needed by the generation argument from
source70, retaining its point-commutator witness. The compatible upper
marking, local actors and exact section centralizer are all constructed
from the genuine earlier setup. The same original subgroups then satisfy
the generation, fixed-kernel, Frattini and derived conclusions of72.
Only the separate earlier13 and68 implications remain explicit here.

Source: Aschbacher–Smith,14.7.70–72,printed pp.1073–1076.
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
theorem generation_from_source_rechoice
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2) (separation : d.ModuleSeparation)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (earlier_conjugacy : ∀ c' : CriticalPath (L := L) F, c'.Zα ≤ V →
      c'.b = 3 ∧ ∃ l ∈ L, c'.Uα = conjugate F.U l)
    (h13 : ∀ n : group F L, SourceGeneration.EarlierThirteen (c.reselect n))
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    SourceGeneration.Conclusion d := by
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
  exact ⟨hout.original_commutator, hout.span_central, hout.span_intersection,
    hout.residual_commutator, hout.actor_commutator, hout.span_join, hout.fixed_kernel,
    hout.fixed_span, hout.seed_central, hout.frattini_eq, hout.derived_eq,
    hout.core_commutator, hout.seed_central_in_Q⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
