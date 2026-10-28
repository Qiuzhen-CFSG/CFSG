module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.DistanceSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicNoncommutingBound

/-!
# Theorem B on the original reduced F.1.11 critical path

The noncommuting branch has distance one or two by the intrinsic source
bound. In the commuting branch, the Chapter 8 theorem supplies the distance
premise to the Chapter 9 reduction, giving distance three whenever it is
larger than one. This is the prime-two specialization of Theorem B.

The full local catalogue and three concrete Chapter 5 binary models are
retained as mathematical inputs. `CommutingTrivial/ModelApplications`
supplies the original linear and Suzuki models; the remaining catalogue
selection belongs to the source assembly. No distance or contradiction
callback is assumed. The field-two conclusion of 9.10 is independent.

Source: DGS, *Groups and Graphs* (1985), Theorem B, p.102;
Chapters 7--9, especially 8.4 and 9.11, pp.137--151.
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
theorem reduced_critical_alternatives_of_catalogue
    (h : HypothesisF11 L S)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S))
    (Ma : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) a)))
    (Mb : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) beta)))
    (Md : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) a'))) :
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
      exact CommutingNontrivial.reduced_commuting_distance_three h
        (Reduction.reduced_graph_core_obstruction h) models hc hab hd hb hcomm Ma Mb Md
    · left
      change b Γ = 1
      omega
  · exact Or.inl ⟨hcomm,Reduction.reduced_intrinsic_noncommuting_bound h hc hcomm⟩

/-- The literal alternatives of DGS Theorem B on the original reduced path.
In the prime-two source, the stronger preceding theorem also excludes five. -/
theorem reduced_theorem_B_of_catalogue
    (h : HypothesisF11 L S)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S))
    (Ma : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) a)))
    (Mb : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) beta)))
    (Md : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) a'))) :
    let Γ := Reduction.reducedFamily L S
    (⁅Z Γ a,Z Γ a'⁆ ≠ ⊥ ∧ (b Γ = 1 ∨ b Γ = 2)) ∨
      (⁅Z Γ a,Z Γ a'⁆ = ⊥ ∧ (b Γ = 1 ∨ b Γ = 3 ∨ b Γ = 5)) := by
  rcases reduced_critical_alternatives_of_catalogue h models hc hab hd Ma Mb Md with hh | ⟨hc,hb⟩
  · exact Or.inl hh
  · exact Or.inr ⟨hc,hb.imp_right Or.inl⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
