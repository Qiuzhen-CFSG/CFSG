module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalVanishing

/-!
# The complete moving-intersection case on the original F1.11 reduction

The reduced triple supplies the full Borel Sylow and the original graph.
The exact earlier local obstruction supplies its earlier-local theorem
package. The complete source-model catalogue then rules out reverse
containment whenever Z_alpha intersect Q_alpha' moves V_alpha'. Both
orientations of the critical pair are allowed; all centers, cores and
radius-one spans are those of the original reduced action.

This discharges the nonzero-intersection subcase of DGS 8.2. The
zero-intersection factor-module subcase and 8.3--8.7 remain with the
Chapter 8 owner. Earlier local obstruction and catalogue exhaustiveness
remain inputs from qt-dgs85-setup-obstruction and final source assembly.
No final distance bound, natural-module assertion or classification
alternative is used as a premise.

Source: DGS, *Groups and Graphs* (1985), 8.2, pp.134--135;
Aschbacher--Smith, F.1.9--F.1.11, for the original reduction.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Under reverse containment, the literal original center/core intersection
centralizes the entire ending span, for the complete source catalogue. -/
theorem reduced_reverse_intersection_centralizes
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
    (hreverse : V (Reduction.reducedFamily J S) a' 1 ≤ Q (Reduction.reducedFamily J S) beta) :
    ⁅Z (Reduction.reducedFamily J S) a ⊓ Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ = ⊥ :=
  source_reverse_intersection_centralizes (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedEarlierLocalTheorems h hob)
    hc hab hd hb hcomm models hreverse

/-- Original reduced F1.11 reciprocal escape in the moving-intersection
subcase. The common-source geometry constructs all graph and Sylow inputs. -/
theorem reduced_reciprocal_escape_of_moving_intersection
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
    (hmove : ⁅Z (Reduction.reducedFamily J S) a ⊓ Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ ≠ ⊥) :
    ¬ V (Reduction.reducedFamily J S) a' 1 ≤ Q (Reduction.reducedFamily J S) beta :=
  source_reciprocal_escape_of_moving_intersection (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedEarlierLocalTheorems h hob)
    hc hab hd hb hcomm models hmove

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
