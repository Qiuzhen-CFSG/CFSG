module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCriticalSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCommutingExclusionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairBTwoOrientation

/-!
# The original alternating-five pair reduces to its noncommuting source

The critical pair and its first edge are chosen inside the genuine F.1.1
graph. The original A5 marks exclude every commuting critical pair, while
the intrinsic distance-one comparison already proves the desired original
core equalities and containments. Thus the only remaining case is an actual
noncommuting distance-two path, with the full middle-parabolic core already
identified with its original factor core in the correct orientation.

The two original quotient marks and single normalized Borel are unchanged.
No critical pair, local catalogue, reduced comparison or classification
callback is supplied by the caller. Alpha residual containment and the
original join-core extension remain necessary in the surviving branch.
-/

public noncomputable section
open Subgroup Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] [Finite G] {K R S : Subgroup G}

/-- The unchanged original A5/A5 pair either already has both core equalities
and containments, or supplies its own noncommuting distance-two source path
with the actual middle core controlled. No source-branch premise remains. -/
theorem a5_pair_original_bTwo_reduction
    (h : HypothesisF11 ![K,R] S)
    (a : ∀ j, Nonempty ((![K,R] j ⧸ pCore 2 (![K,R] j)) ≃*
      alternatingGroup (Fin 5)))
    (hnorm : ∃ j, borel (![K,R] j) S ≤ normalizer (S : Set G)) :
    ((∀ j, twoCore (![K,R] j ⊔ S) = twoCore (![K,R] j)) ∧
      (∀ j, S ≤ ![K,R] j)) ∨
    ∃ (i : Bool) (w : Vertex (reducedFamily ![K,R] S)),
      IsCriticalPair (reducedFamily ![K,R] S)
        (base (reducedFamily ![K,R] S) i) w ∧
      b (reducedFamily ![K,R] S) = 2 ∧
      (graph (reducedFamily ![K,R] S)).Adj
        (base (reducedFamily ![K,R] S) (!i)) w ∧
      ⁅Z (reducedFamily ![K,R] S) (base (reducedFamily ![K,R] S) i),
        Z (reducedFamily ![K,R] S) w⁆ ≠ ⊥ ∧
      twoCore (parabolic ![K,R] S (if i then 0 else 1)) =
        twoCore (![K,R] (if i then 0 else 1)) := by
  rcases a5_pair_original_critical_selection h a hnorm with hdone |
    ⟨i, w, hc, _, hnc | hcomm⟩
  · exact .inl hdone
  · obtain ⟨hb, hmw, hne⟩ := hnc
    exact .inr ⟨i, w, hc, hb, hmw, hne,
      h.a5_bTwo_middle_parabolic_core_eq a i hc hne hb hmw⟩
  · exact (a5_pair_critical_not_commuting h a hc hcomm.2.1).elim

end CFSG.Quasithin.ChapterF.Source
