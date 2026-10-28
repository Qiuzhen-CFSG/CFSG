module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairBTwoAlphaCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairBTwoOrientation

/-!
# Both original parabolic cores in either critical orientation

The actual critical path can start in either original vertex orbit.
The frozen original-pair reorientation transports its full kernel escape,
noncommuting centers, and middle edge. The alpha and beta source theorems
therefore identify both full parabolic cores with the original factor cores.
No assertion about adjoining S to an original factor is inferred here.
-/

public noncomputable section
open Subgroup Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] [Finite G] {K R S : Subgroup G}

/-- The full alpha parabolic core is the original factor core in the
actual orientation of the critical pair. -/
theorem HypothesisF11.a5_bTwo_start_parabolic_core_eq
    (h : HypothesisF11 ![K,R] S)
    (a : ∀ j, Nonempty ((![K,R] j ⧸ pCore 2 (![K,R] j)) ≃*
      alternatingGroup (Fin 5)))
    (i : Bool) {w : Vertex (reducedFamily ![K,R] S)}
    (hc : IsCriticalPair (reducedFamily ![K,R] S)
      (base (reducedFamily ![K,R] S) i) w)
    (hne : ⁅Z (reducedFamily ![K,R] S) (base (reducedFamily ![K,R] S) i),
      Z (reducedFamily ![K,R] S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily ![K,R] S) = 2)
    (hmw : (graph (reducedFamily ![K,R] S)).Adj
      (base (reducedFamily ![K,R] S) (!i)) w) :
    twoCore (parabolic ![K,R] S (if i then 1 else 0)) =
      twoCore (![K,R] (if i then 1 else 0)) := by
  cases i
  · exact h.a5_bTwo_alpha_parabolic_core_eq a hc hne hb hmw
  · obtain ⟨w',hc',hne',hmw'⟩ :=
      CriticalReorientation.original_noncommuting_critical_swap K R S hc hne hmw
    have a' : ∀ j, Nonempty ((![R,K] j ⧸ pCore 2 (![R,K] j)) ≃*
        alternatingGroup (Fin 5)) := by
      intro j
      fin_cases j
      · exact a 1
      · exact a 0
    have hb' : b (reducedFamily ![R,K] S) = 2 := (pair_b_swap K R S).trans hb
    exact h.swap.a5_bTwo_alpha_parabolic_core_eq a' hc' hne' hb' hmw'

/-- Both full original parabolic cores are controlled by the actual
noncommuting distance-two path, whichever original factor starts it. -/
theorem HypothesisF11.a5_bTwo_parabolic_cores_eq
    (h : HypothesisF11 ![K,R] S)
    (a : ∀ j, Nonempty ((![K,R] j ⧸ pCore 2 (![K,R] j)) ≃*
      alternatingGroup (Fin 5)))
    (i : Bool) {w : Vertex (reducedFamily ![K,R] S)}
    (hc : IsCriticalPair (reducedFamily ![K,R] S)
      (base (reducedFamily ![K,R] S) i) w)
    (hne : ⁅Z (reducedFamily ![K,R] S) (base (reducedFamily ![K,R] S) i),
      Z (reducedFamily ![K,R] S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily ![K,R] S) = 2)
    (hmw : (graph (reducedFamily ![K,R] S)).Adj
      (base (reducedFamily ![K,R] S) (!i)) w) :
    ∀ j, twoCore (parabolic ![K,R] S j) = twoCore (![K,R] j) := by
  have ha := h.a5_bTwo_start_parabolic_core_eq a i hc hne hb hmw
  have hm := h.a5_bTwo_middle_parabolic_core_eq a i hc hne hb hmw
  intro j
  cases i <;> fin_cases j
  · exact ha
  · exact hm
  · exact hm
  · exact ha

end CFSG.Quasithin.ChapterF.Source
