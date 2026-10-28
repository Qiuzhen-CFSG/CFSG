module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OppositeResidualMovement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RankOneTerminalDistance

/-!
# The literal reduced-source residual obstruction in DGS 8.5

The opposite residual moves H intersect Z_alpha' on the original reduced
F1.11 graph, at every ordered distance-three critical pair. For PSL₂(2),
D₁₀, Sz(2), PSU₃(2) and SU₃(2) terminal quotients the proved radius-three
argument supplies that distance, with every starting model retained.
The residual is literally the image of pResidual 2 under the original
local inclusion; the denominator is its centralizer in V_beta.

This discharges the final geometric contradiction of 8.5. The natural
module supposition must still be shown to put H in that denominator;
8.5 nonnaturality itself is not asserted here. General distance three
and the remaining 8.6--8.7 assembly also stay separate.

Source: DGS, *Groups and Graphs* (1985), 8.4--8.5, pp.138--139.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The actual source commutator cannot be killed by the opposite residual
fixed quotient at distance three, in either orientation. -/
theorem reduced_distance_three_critical_commutator_not_residual_fixed
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
    (hb : b (Reduction.reducedFamily J S₀) = 3)
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
 :
    let F := Reduction.reducedFamily J S₀
    let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
    let E := (pResidual 2 (graphLocalGroup F beta)).map (graphLocalGroup F beta).subtype
    (¬ H ⊓ Z F a' ≤ centralizer (E : Set (Reduction.G₀ J S₀))) ∧
      ¬ H ≤ V F beta 1 ⊓ centralizer (E : Set (Reduction.G₀ J S₀)) := by
  exact source_distance_three_critical_commutator_not_residual_fixed
    (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h)
    (Reduction.reducedEarlierLocalTheorems h hob) hob models hc hab hd hb hcomm hne

/-- All five small terminal models supply distance three, so the original
hypotheses already force movement of the terminal-center intersection. -/
theorem reduced_small_terminal_critical_commutator_not_residual_fixed
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
    (hsmall :
      let D := graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')
      ClassicalGroup.IsPSL D 2 2 ∨ Nonempty (D ≃* DihedralGroup 5) ∨
      Nonempty (D ≃* SuzukiMatrixGroup 0) ∨ ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2) :
    b (Reduction.reducedFamily J S₀) = 3 ∧
    let F := Reduction.reducedFamily J S₀
    let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
    let E := (pResidual 2 (graphLocalGroup F beta)).map (graphLocalGroup F beta).subtype
    (¬ H ⊓ Z F a' ≤ centralizer (E : Set (Reduction.G₀ J S₀))) ∧
      ¬ H ≤ V F beta 1 ⊓ centralizer (E : Set (Reduction.G₀ J S₀)) := by
  have hb3 := reduced_small_terminal_distance_three h hob models hc hab hd hb hcomm hne hsmall
  exact ⟨hb3,reduced_distance_three_critical_commutator_not_residual_fixed
    h hob models hc hab hd hb3 hcomm hne⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
