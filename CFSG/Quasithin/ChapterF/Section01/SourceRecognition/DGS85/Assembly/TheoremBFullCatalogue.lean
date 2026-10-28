module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.CommutingTrivialChapterEightSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicNoncommutingBound

/-!
# Theorem B with the full source catalogue

The nonzero commuting displacement branch has distance three by Chapter 8.
The zero branch now has distance three by the proved Chapter 9 source
consumer. Together with the intrinsic noncommuting bound, this gives the
original critical alternatives without any supplied binary-model witnesses.

Source: DGS, *Groups and Graphs* (1985), Theorem B, p.102,
and Chapters 8–9, pp.137–151.
-/

@[expose] public noncomputable section
open Subgroup
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The characteristic-two critical alternatives, with the original source
6.5 obstruction and Chapter 8 distance premise discharged. -/
theorem reduced_critical_alternatives_from_full_catalogue
    (h : HypothesisF11 L S)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S)) :
    let Γ := Reduction.reducedFamily L S
    (⁅Z Γ a,Z Γ a'⁆ ≠ ⊥ ∧ (b Γ = 1 ∨ b Γ = 2)) ∨
      (⁅Z Γ a,Z Γ a'⁆ = ⊥ ∧ (b Γ = 1 ∨ b Γ = 3)) := by
  let Γ := Reduction.reducedFamily L S
  by_cases hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥
  · right
    refine ⟨hcomm,?_⟩
    have hp : 0 < b Γ := source_b_positive (Reduction.reduced_triple h)
    by_cases hb : 1 < b Γ
    · right
      by_cases htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥
      · exact (CommutingTrivial.reduced_critical_fields_two_from_chapterEight
          h models hc hab hd hb hcomm htriv).1
      · exact CommutingNontrivial.reduced_distance_three_of_catalogue
          h models hc hab hd hb hcomm htriv
    · left
      change b Γ = 1
      omega
  · exact Or.inl ⟨hcomm,Reduction.reduced_intrinsic_noncommuting_bound h hc hcomm⟩

/-- The literal alternatives of DGS Theorem B on the original reduced path.
In the prime-two source, the stronger preceding theorem also excludes five. -/
theorem reduced_theorem_B_from_full_catalogue
    (h : HypothesisF11 L S)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S)) :
    let Γ := Reduction.reducedFamily L S
    (⁅Z Γ a,Z Γ a'⁆ ≠ ⊥ ∧ (b Γ = 1 ∨ b Γ = 2)) ∨
      (⁅Z Γ a,Z Γ a'⁆ = ⊥ ∧ (b Γ = 1 ∨ b Γ = 3 ∨ b Γ = 5)) := by
  rcases reduced_critical_alternatives_from_full_catalogue h models hc hab hd with hh | ⟨hc,hb⟩
  · exact Or.inl hh
  · exact Or.inr ⟨hc,hb.imp_right Or.inl⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
