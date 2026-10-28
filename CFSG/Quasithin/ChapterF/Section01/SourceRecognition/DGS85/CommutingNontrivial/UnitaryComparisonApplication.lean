module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryComparison
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.EscapeApplication

/-!
# Original reduced-source application of the Chapter 8.3 comparison

The actual reduced F1.11 graph supplies the full-edge Sylow, original local
quotient and moving neighbor. Reciprocal escape is already proved for the
complete source catalogue. The terminal 8.3 argument now supplies the full
quotient-omega commutator inclusion once the two comparisons in (8.3)(2)
are established. Those comparisons are explicit remaining obligations of
the Chapter 8 owner, not earlier-source inputs or classification outputs.

All critical orientations, source 6.5 nonnormality and actual quotient models
are retained. Source: DGS, Groups and Graphs (1985), 8.2--8.3, pp.134--137.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The original reduced-source consumer of the complete terminal comparison.
Only the paired factor-module comparisons of 8.3(2) remain to be constructed
locally; reciprocal escape and all terminal index premises are discharged. -/
theorem reduced_omega_commutator_of_paired_indices
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
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,
      Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓
      Q (Reduction.reducedFamily J S₀) a',V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hpair : let F := Reduction.reducedFamily J S₀
      ∀ w : (graph F).neighborSet a',
        ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥ →
        ∀ n : ℕ, 2 ≤ n →
          (ClassicalGroup.IsPSU (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) 3 (2^n) ∨
            IsSU (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) 3 (2^n)) →
          (Q F a').relIndex (V F beta 1) ^ 2 ≤ (Q F beta).relIndex (V F a' 1) * 2^n ∧
          (Q F beta).relIndex (V F a' 1) ^ 2 ≤ (Q F a').relIndex (V F beta 1) * 2^n) :
    let F := Reduction.reducedFamily J S₀
    ¬ V F a' 1 ≤ Q F beta ∧
      ∃ w : (graph F).neighborSet a',
        ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥ ∧
        ∃ R : Sylow 2 (graphLocalGroup F w.val),
          (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype =
            (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ∧
          ⁅quotientSylowOmegaPreimage (graphLocalGroup F w.val) R,Z F w.val⁆ ≤
            ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have he := reduced_reciprocal_escape h hob models hc hab hd hb hcomm hne
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d w.property.symm
  exact ⟨he,w,hm,R,hR,source_omega_commutator_of_paired_indices ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models w hm R hR (hpair w hm)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
