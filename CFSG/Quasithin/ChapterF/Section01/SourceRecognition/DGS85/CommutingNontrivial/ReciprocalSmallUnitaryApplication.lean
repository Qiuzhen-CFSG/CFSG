module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalSmallUnitary

/-!
# The large-unitary reciprocal remainder on the reduced F1.11 graph

The original source reduction supplies the full Borel Sylow, local groups,
and original quotient maps. The new rank-one image argument excludes both
field-two unitary rows without assuming full action faithfulness. Thus a
nonzero moving intersection under reverse containment has a marked SU₃ or
PSU₃ quotient of field order at least four and a neighboring core of index
two in the original intersection. The critical pair is arbitrary, so the
application is compatible with reorientation.

The earlier 6.1 model markings and 6.5 obstruction retain their existing
producers. The Chapter 8 owner retains the large-unitary involution and
factor-module arguments; final source assembly retains all earlier premise
discharge.

Source: DGS, *Groups and Graphs* (1985), (8.2), pp.134--135, and
Aschbacher--Smith F.1.9--F.1.11 for the original reduction.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Literal reduced-source application of the complete moving-intersection
catalogue comparison, with an actual neighboring vertex witness. -/
theorem reduced_reverse_moving_intersection_large_unitary_witness
    (h : HypothesisF11 J S)
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
    (hreverse : V (Reduction.reducedFamily J S) a' 1 ≤ Q (Reduction.reducedFamily J S) beta)
    (hmove : ⁅Z (Reduction.reducedFamily J S) a ⊓ Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ ≠ ⊥)
    : ∃ n : ℕ, 2 ≤ n ∧
      (ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S) a ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a)) 3 (2^n) ∨
        IsSU (graphLocalGroup (Reduction.reducedFamily J S) a ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a)) 3 (2^n)) ∧
      (∀ w : (graph (Reduction.reducedFamily J S)).neighborSet a',
        (Q (Reduction.reducedFamily J S) w.val).relIndex
          (Z (Reduction.reducedFamily J S) a ⊓ Q (Reduction.reducedFamily J S) a') ≤ 2) ∧
      ∃ w : (graph (Reduction.reducedFamily J S)).neighborSet a',
        ⁅Z (Reduction.reducedFamily J S) a ⊓ Q (Reduction.reducedFamily J S) a',
          Z (Reduction.reducedFamily J S) w.val⁆ ≠ ⊥ ∧
        (Q (Reduction.reducedFamily J S) w.val).relIndex
          (Z (Reduction.reducedFamily J S) a ⊓ Q (Reduction.reducedFamily J S) a') = 2 := by
  exact source_reverse_moving_intersection_large_unitary_witness (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedEarlierLocalTheorems h hob)
    hc hab hd hb hcomm models hreverse hmove

/-- The two field-two unitary cases vanish on the literal reduced span;
the quotient marking and original critical orientation are unchanged. -/
theorem reduced_reverse_small_unitary_intersection_centralizes
    (h : HypothesisF11 J S)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S),
      (graph (Reduction.reducedFamily J S)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S) w ⊓ Q (Reduction.reducedFamily J S) v :
          Subgroup (Reduction.G₀ J S)) : Set (Reduction.G₀ J S)))
    {a beta a' : Vertex (Reduction.reducedFamily J S)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S) a a')
    (hab : (graph (Reduction.reducedFamily J S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S)).dist beta a' + 1 = b (Reduction.reducedFamily J S))
    (hb : 1 < b (Reduction.reducedFamily J S))
    (hcomm : ⁅Z (Reduction.reducedFamily J S) a,Z (Reduction.reducedFamily J S) a'⁆ = ⊥)
    (hreverse : V (Reduction.reducedFamily J S) a' 1 ≤ Q (Reduction.reducedFamily J S) beta)
    (hmodel : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S) a ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a)) 3 2 ∨
        IsSU (graphLocalGroup (Reduction.reducedFamily J S) a ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a)) 3 2) :
    ⁅Z (Reduction.reducedFamily J S) a ⊓ Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ = ⊥ :=
  source_reverse_small_unitary_intersection_centralizes (Reduction.reduced_triple h)
    (Reduction.reducedEarlierLocalTheorems h hob) hc hab hd hb hcomm hreverse hmodel

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
