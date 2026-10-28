module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LocalGeneration

/-!
# Reduced-source application of the Chapter 8 normality argument

The original F1.11 hypotheses construct the reduced source graph, its exact
full-edge Sylows, local actors and kernel-Sylow equality. The local generation
and displacement proofs now give 8.1(g,i) for every ordered critical pair:
H is normal in L_alpha', lies in every neighboring center, and its centralizer
cannot have the neighboring core as a Sylow subgroup. The nonzero commutator
selects a moving neighbor with the actual full-edge Sylow, not an abstract
actor of the same order. The source 6.1 quotient models and 6.5 obstruction
remain genuine earlier inputs supplied by the shared source assembly.

Source: DGS, *Groups and Graphs* (1985), 8.0 and 8.1(g,i), pp.132--133.
This is a conditional earlier-input application; it does not establish the
later b=3, equal-field or natural-module conclusions of 8.4--8.7.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- Literal reduced-F1.11 application of 8.1(g,i). The source construction
supplies every earlier graph field except 6.5. Its actual local quotient
models are the earlier 6.1 input; neither generation nor displacement is
assumed. The ordered critical pair is arbitrary, allowing reorientation. -/
theorem reduced_critical_commutator_structure
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
    (hcomm : ⁅Z (Reduction.reducedFamily J S) a, Z (Reduction.reducedFamily J S) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S) beta 1 ⊓ Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ ≠ ⊥) :
    let F := Reduction.reducedFamily J S
    let H := ⁅V F beta 1 ⊓ Q F a', V F a' 1⁆
    Odd (b F) ∧ 3 ≤ b F ∧
      (H.subgroupOf (graphLocalGroup F a')).Normal ∧
      (∀ w : (graph F).neighborSet a', H ≤ Z F w.val) ∧
      ∃ w : (graph F).neighborSet a',
        ⁅V F beta 1 ⊓ Q F a', Z F w.val⁆ ≠ ⊥ ∧
        (∃ T : Sylow 2 ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (Reduction.G₀ J S)),
          V F beta 1 ⊔ (T : Subgroup ↥(stabilizer F a' ⊓ stabilizer F w.val :
            Subgroup (Reduction.G₀ J S))).map (stabilizer F a' ⊓ stabilizer F w.val).subtype =
              graphLocalGroup F a' ∧
          ⁅(T : Subgroup ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (Reduction.G₀ J S))).map
            (stabilizer F a' ⊓ stabilizer F w.val).subtype, V F beta 1 ⊓ Q F a'⁆ ≤ Q F w.val) ∧
        ¬ ∃ T : Sylow 2 ↥(graphLocalGroup F a' ⊓ centralizer (H : Set (Reduction.G₀ J S)) :
            Subgroup (Reduction.G₀ J S)),
          (T : Subgroup ↥(graphLocalGroup F a' ⊓ centralizer (H : Set (Reduction.G₀ J S)) :
            Subgroup (Reduction.G₀ J S))).map
              (graphLocalGroup F a' ⊓ centralizer (H : Set (Reduction.G₀ J S))).subtype = Q F w.val := by
  dsimp only
  let h' := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  obtain ⟨hodd, hb3, _⟩ := source_critical_geometry h' d hc hab hd hb hcomm
  obtain ⟨hn, hcen, hobs⟩ := source_critical_commutator_structure h'
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models
  obtain ⟨w, hw, _⟩ := exists_moving_neighbor (Reduction.reducedFamily J S)
    (fun v => (source_Z_Q_U h' v).1) beta a' hne
  obtain ⟨T, hT⟩ := source_moving_edge_generation h' (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm (models a') w hw
  exact ⟨hodd, hb3, hn, hcen, w, hw,
    ⟨T, hT, source_moving_actor_displacement h' d hc hab hd hb hcomm w (models w.val) T⟩,
    hobs w⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
