module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairBTwoBetaSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalReorientation

/-!
# The actual beta core in either original orientation

The intrinsic critical pair may start in either original vertex orbit.
Exchanging the two original factors transports the whole critical path and
its noncommuting centers, so the beta core source applies to the actual
middle endpoint in both orientations. This does not identify the opposite
alpha core or assert the remaining original join-core equalities.
-/

public noncomputable section
open Subgroup Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction

variable {G : Type*} [Group G] [Finite G] {K R S : Subgroup G}

/-- The full middle-parabolic core is the original factor core for the
literal distance-two critical path, with either original alpha type. -/
theorem HypothesisF11.a5_bTwo_middle_parabolic_core_eq
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
    twoCore (parabolic ![K,R] S (if i then 0 else 1)) =
      twoCore (![K,R] (if i then 0 else 1)) := by
  cases i
  · exact h.a5_bTwo_beta_parabolic_core_eq a hc hne hb hmw
  · obtain ⟨w', hc', hne', hmw'⟩ :=
      CriticalReorientation.original_noncommuting_critical_swap K R S hc hne hmw
    have a' : ∀ j, Nonempty ((![R,K] j ⧸ pCore 2 (![R,K] j)) ≃*
        alternatingGroup (Fin 5)) := by
      intro j
      fin_cases j
      · exact a 1
      · exact a 0
    have hb' : b (reducedFamily ![R,K] S) = 2 := (pair_b_swap K R S).trans hb
    exact h.swap.a5_bTwo_beta_parabolic_core_eq a' hc' hne' hb' hmw'

end CFSG.Quasithin.ChapterF.Source
