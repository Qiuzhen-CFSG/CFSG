module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalCatalogue

/-!
# The reciprocal catalogue comparison on the actual F1.11 reduction

The original source reduction supplies the full Borel Sylow, local groups,
and all original quotient maps. If a nonzero intersection in the second
subcase of 8.2 coexists with reverse containment, the starting local quotient
is SU₃ or PSU₃ and an actual neighbor sees an image of order exactly two.
The entire source catalogue, including the small and dihedral rows, is
handled by the imported comparison. Reorientation is allowed because the
critical pair and its first edge are arbitrary.

The existing 6.1 model producer and 6.5 obstruction remain explicit earlier
inputs. The Chapter 8 owner retains the involution and factor-module cases,
and the source assembly retains discharge of every earlier input.

Source: DGS, *Groups and Graphs* (1985), (8.2), pp.134--135;
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
theorem reduced_reverse_moving_intersection_unitary_witness
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
    : ∃ n : ℕ, 0 < n ∧
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
  exact source_reverse_moving_intersection_unitary_witness (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedEarlierLocalTheorems h hob)
    hc hab hd hb hcomm models hreverse hmove

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
