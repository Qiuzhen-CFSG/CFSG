module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearCenterExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearNoncentralObstruction
/-!
# Both DGS adjacent-core obstructions for arbitrary linear endpoint fields

Contrary relative normality supplies the (6.4) premises. The natural-module
argument excludes the central-center case at every field size. The proved
noncentral core-pair contradiction then excludes that relative normality;
the Sylow-to-normality implication excludes the Sylow assertion as well.
Both original endpoint fields may differ. General rank-one model selection
remains an earlier source obligation outside this linear specialization.

Source: DGS, Groups and Graphs (1985), (6.5), pp.121--122.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
/-- Both 6.5 clauses  for arbitrary marked linear endpoint fields. -/
theorem source_linear_adjacent_core_obstruction (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (j : Bool) (d : LocalRankOneData (family P (!j)) B)
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d))
    (eδ : (graphLocalGroup (family P) (base (family P) j) ⧸
      pCore 2 (graphLocalGroup (family P) (base (family P) j))) ≃* SL(2,K)) :
    (¬ localEnlargement d ≤ normalizer
      (↑((family P j).pCoreIn 2 ⊓ (family P (!j)).pCoreIn 2) : Set G)) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j))),
      (T : Subgroup (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j)))).map
        (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j))).subtype = (family P j).pCoreIn 2 := by
  have hnot : ¬ localEnlargement d ≤ normalizer
      (↑((family P j).pCoreIn 2 ⊓ (family P (!j)).pCoreIn 2) : Set G) := by
    intro hn
    have hnc : ¬ sylowCenterSpan (family P (!j)) ≤ centralizer
        (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j)) : Set G) := by
      cases j
      · exact source_linear_neighbor_center_noncentral h hB hS 0 d hn q hq hk
      · exact source_linear_neighbor_center_noncentral h hB hS 1 d hn q hq hk
    exact (source_linear_noncentral_adjacent_core_obstruction h hB hS j d q hq hk hnc eδ).1 hn
  refine ⟨hnot, ?_⟩
  have hnfull : ¬ family P (!j) ≤ normalizer
      (↑((family P j).pCoreIn 2 ⊓ (family P (!j)).pCoreIn 2) : Set G) :=
    fun hn => hnot ((localEnlargement_le d).trans hn)
  cases j
  · exact core_not_sylow_of_inter_not_normal h 0 hnfull
  · exact core_not_sylow_of_inter_not_normal h 1 hnfull
end CFSG.Quasithin.ChapterF.Source.DGS85
