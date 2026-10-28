module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairOriginalReduction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairBTwoCoreOrientation

/-!
# Original A5 pair reduction with both full parabolic cores

Consume the frozen original critical-pair reduction and the alpha/beta
source core theorems. The surviving branch retains its actual critical
path and has both full parabolic cores equal to the original factor cores.
The original one-normalized-Borel hypothesis is unchanged. Extending these
equalities to the local joins still requires the source outer-action step.
-/

public noncomputable section
open Subgroup Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] [Finite G] {K R S : Subgroup G}

/-- Either both original containments and join-core equalities already hold,
or the actual distance-two source has both full parabolic cores controlled. -/
theorem a5_pair_original_bTwo_core_reduction
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
      (∀ j, twoCore (parabolic ![K,R] S j) = twoCore (![K,R] j)) := by
  rcases a5_pair_original_bTwo_reduction h a hnorm with hdone |
    ⟨i,w,hc,hb,hmw,hne,_⟩
  · exact .inl hdone
  · exact .inr ⟨i,w,hc,hb,hmw,hne,h.a5_bTwo_parabolic_cores_eq a i hc hne hb hmw⟩

/-- The unchanged original hypotheses identify both full parabolic cores.
This statement does not identify either local-join core. -/
theorem a5_pair_original_parabolic_cores_eq
    (h : HypothesisF11 ![K,R] S)
    (a : ∀ j, Nonempty ((![K,R] j ⧸ pCore 2 (![K,R] j)) ≃*
      alternatingGroup (Fin 5)))
    (hnorm : ∃ j, borel (![K,R] j) S ≤ normalizer (S : Set G)) :
    ∀ j, twoCore (parabolic ![K,R] S j) = twoCore (![K,R] j) := by
  rcases a5_pair_original_bTwo_core_reduction h a hnorm with ⟨_,hS⟩ |
    ⟨_,_,_,_,_,_,hcore⟩
  · intro j
    rw [←h.local_inf_parabolic_core j]
    exact (inf_eq_right.mpr ((h.parabolic_core_le_S j).trans (hS j))).symm
  · exact hcore

end CFSG.Quasithin.ChapterF.Source
