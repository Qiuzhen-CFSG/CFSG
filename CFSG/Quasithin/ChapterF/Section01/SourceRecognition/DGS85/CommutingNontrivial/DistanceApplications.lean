module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.DistanceThree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OppositeResidualApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceReduction

/-!
# Original consumers of the Chapter 8 distance theorem

The nontrivial commuting theorem supplies Chapter 9's distance premise at
all ordered critical pairs, including shifted and reversed configurations.
Applying it to the original Chapter 9 distance reduction removes that
premise there. The existing opposite-residual obstruction also applies
without a small-terminal or distance-three assumption.

The original local catalogue and 6.5 obstruction remain explicit. These
applications do not supply the natural-module exclusion of 8.5, the center
and field identifications of 8.6--8.7, or Chapter 9's separate natural
reorientation premise.

Source: DGS, *Groups and Graphs* (1985), 8.4--8.5 and 9.11,
pp.137--139,150--151.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The actual Chapter 9 distance premise, uniformly in both critical orientations. -/
theorem reduced_chapter_eight_distance
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    : CommutingTrivial.ChapterEightDistance (Reduction.reducedFamily J S₀) := by
  intro a beta a' hc hab hd hb hcomm hne
  exact reduced_distance_three h hob models hc hab hd hb hcomm hne

/-- The opposite residual moves the original critical commutator for every local model. -/
theorem reduced_critical_commutator_not_residual_fixed
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    :
    let F := Reduction.reducedFamily J S₀
    let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
    let E := (pResidual 2 (graphLocalGroup F beta)).map (graphLocalGroup F beta).subtype
    (¬ H ⊓ Z F a' ≤ centralizer (E : Set (Reduction.G₀ J S₀))) ∧
      ¬ H ≤ V F beta 1 ⊓ centralizer (E : Set (Reduction.G₀ J S₀)) := by
  exact reduced_distance_three_critical_commutator_not_residual_fixed h hob models hc hab hd
    (reduced_distance_three h hob models hc hab hd hb hcomm hne) hcomm hne

/-- Chapter 9's distance conclusion with its Chapter 8 distance premise discharged.
The three original binary representation models are retained verbatim. -/
theorem reduced_commuting_distance_three
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a'))) :
    b (Reduction.reducedFamily J S₀) = 3 := by
  exact CommutingTrivial.reduced_critical_distance_eq_three h hc hab hd hb hcomm
    (reduced_chapter_eight_distance h hob models) hob Mα Mβ Mα' (models a)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
