module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaCommutator

/-!
# Original reduced-source application of the DGS 8.3 unitary reduction

Choose a moving neighbor from the original nonzero H and construct its
full-edge Sylow inside the actual local group. The full quotient omega-center
then has commutator in H, or the same local quotient has an actual SU₃ or
PSU₃ marking over a field of order at least four. All other source models,
including small parameters and D₁₀, are discharged by `OmegaCommutator`.

The output retains the original reduced F1.11 graph, local group, chosen
Sylow image and quotient preimage. This is the reduction (8.3)(1), not the
remaining unitary contradiction or the final Chapter 8 classification.
Source: DGS, *Groups and Graphs* (1985), (8.3), printed p.135.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]

/-- The full quotient-omega reduction at an actually selected moving
neighbor and an actually constructed edge Sylow of the reduced source. -/
theorem reduced_moving_omega_commutator_or_large_unitary
    {J : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 J S)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S),
      (graph (Reduction.reducedFamily J S)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S) w ⊓ Q (Reduction.reducedFamily J S) v :
          Subgroup (Reduction.G₀ J S)) : Set (Reduction.G₀ J S)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S) a a')
    (hab : (graph (Reduction.reducedFamily J S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S)).dist beta a' + 1 = b (Reduction.reducedFamily J S))
    (hb : 1 < b (Reduction.reducedFamily J S))
    (hcomm : ⁅Z (Reduction.reducedFamily J S) a,Z (Reduction.reducedFamily J S) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S) beta 1 ⊓ Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ ≠ ⊥) :
    let F := Reduction.reducedFamily J S
    ∃ w : (graph F).neighborSet a',
      ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥ ∧
      ∃ R : Sylow 2 (graphLocalGroup F w.val),
        (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype =
          (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ∧
        (⁅quotientSylowOmegaPreimage (graphLocalGroup F w.val) R,Z F w.val⁆ ≤
            ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ∨
          ∃ n : ℕ, 2 ≤ n ∧
            (ClassicalGroup.IsPSU (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) 3 (2^n) ∨
              IsSU (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) 3 (2^n))) := by
  dsimp only
  let h' := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor (Reduction.reducedFamily J S)
    (fun v => (source_Z_Q_U h' v).1) beta a' hne
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h' (Reduction.reduced_borel_core_sylow h) d
    (show (graph (Reduction.reducedFamily J S)).Adj a' w.val from w.property).symm
  exact ⟨w,hm,R,hR,source_moving_omega_commutator_or_large_unitary h'
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models w hm R hR⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
