module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ModelApplications

/-!
# Original linear models in the small-neighbor Chapter 9 input

The source rows are the authoritative model hypotheses. This application
extracts the actual graph quotient markings and discharges the complete 6.5
edge obstruction before a later small-neighbor consumer invokes its linear
conclusion theorem.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Original linear source rows provide both actual endpoint markings and the
full reduced-graph 6.5 obstruction needed by the small-neighbor consumer. -/
theorem reduced_small_neighbor_linear_inputs_of_original_models
    (h : HypothesisF11 L S)
    {a beta : Vertex (Reduction.reducedFamily L S)}
    (hm : ∀ i : Bool, ∃ n : ℕ,
      0 < n ∧ ClassicalGroup.IsPSL
        (family L i ⧸ pCore 2 (family L i)) 2 (2 ^ n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (n m : ℕ),
      0 < n ∧ Nat.card F = 2 ^ n ∧
      0 < m ∧ Nat.card K = 2 ^ m ∧
      ∃ _eα : (graphLocalGroup (Reduction.reducedFamily L S) a ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) a)) ≃* SL(2, F),
        ∃ _eβ : (graphLocalGroup (Reduction.reducedFamily L S) beta ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) beta)) ≃* SL(2, K),
          ∀ {v w : Vertex (Reduction.reducedFamily L S)},
            (graph (Reduction.reducedFamily L S)).Adj v w →
            ¬ stabilizer (Reduction.reducedFamily L S) v ≤ normalizer
              ((Q (Reduction.reducedFamily L S) w ⊓
                Q (Reduction.reducedFamily L S) v :
                Subgroup (Reduction.G₀ L S)) : Set (Reduction.G₀ L S)) := by
  obtain ⟨F, hF, hFfin, hFchar, K, hK, hKfin, hKchar, n, m,
      hn, hFcard, hmpos, hKcard, ⟨eα⟩, ⟨eβ⟩⟩ :=
    reduced_original_linear_vertex_markings h hm a beta
  exact ⟨F, hF, hFfin, hFchar, K, hK, hKfin, hKchar, n, m,
    hn, hFcard, hmpos, hKcard, eα, eβ,
    fun hvw => reduced_original_linear_graph_core_obstruction h hm hvw⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
