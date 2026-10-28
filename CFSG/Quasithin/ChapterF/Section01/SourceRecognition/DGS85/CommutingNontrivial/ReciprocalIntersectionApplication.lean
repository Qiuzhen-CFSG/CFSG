module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalIntersection

/-!
# The moving-intersection subcase on the original reduced source graph

The original F1.11 reduction supplies the full Borel core Sylow and the
literal earlier local data, retaining the 6.1 model markings and 6.5
obstruction as earlier inputs. A nonzero commutator of Z_alpha intersect
Q_alpha' with V_alpha' now forces reciprocal escape in both the linear and
Suzuki rows. Conjugation transports the same quotient model to every
moving neighbor; no matching-field or numerical estimate is assumed.

Source: DGS, *Groups and Graphs* (1985), (8.2), second subcase, p.135;
Aschbacher--Smith F.1.9 and F.1.11 for the original reduction. This does not
settle the first subcase or the unitary rows. The Chapter 8 owner retains
these and all later conclusions, with final source assembly discharging the
earlier 6.1 and 6.5 inputs.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Original reduced F1.11 application of the linear moving-intersection
subcase of 8.2, at any orientation of the critical pair. -/
theorem reduced_linear_reciprocal_escape_of_moving_intersection
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
      V (Reduction.reducedFamily J S) a' 1⁆ ≠ ⊥)
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily J S) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a)) ≃* SL(2,K)) :
    ¬ V (Reduction.reducedFamily J S) a' 1 ≤ Q (Reduction.reducedFamily J S) beta := by
  intro hreverse
  exact hmove (source_reverse_linear_intersection_centralizes (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedEarlierLocalTheorems h hob)
    hc hab hd hb hcomm models hreverse hn hK e)

/-- Original reduced F1.11 application of the Suzuki moving-intersection
subcase of 8.2. The parameter-zero model Sz(2) is included. -/
theorem reduced_suzuki_reciprocal_escape_of_moving_intersection
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
    (hmove : ⁅Z (Reduction.reducedFamily J S) a ⊓ Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ ≠ ⊥)
    (m : ℕ) (e : (graphLocalGroup (Reduction.reducedFamily J S) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a)) ≃* SuzukiMatrixGroup m) :
    ¬ V (Reduction.reducedFamily J S) a' 1 ≤ Q (Reduction.reducedFamily J S) beta := by
  intro hreverse
  exact hmove (source_reverse_suzuki_intersection_centralizes (Reduction.reduced_triple h)
    (Reduction.reducedEarlierLocalTheorems h hob) hc hab hd hb hcomm hreverse m e)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
