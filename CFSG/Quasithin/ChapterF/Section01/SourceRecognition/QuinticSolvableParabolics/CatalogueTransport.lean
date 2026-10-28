module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.QuinticSolvableParabolics.ReducedSylow
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Action

/-!
# The quintic constraints on a reduced model

The original containment S ≤ K identifies the reduced Sylow with S. Thus
the first reduced endpoint is solvable and its full overlap has index five.
These facts transport even through parabolic equivalence: only the actual
endpoint and overlap isomorphisms are needed for the order calculation.

Source: Aschbacher–Smith F.1.10–12, pp.262–264; DGS (15.1), p.226.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.QuinticSolvableParabolics
open SuzukiContainment DGS85.OriginalExtension
variable {G : Type*} [Group G] {K R S : Subgroup G}

/-- The literal first reduced endpoint is solvable. -/
theorem reduced_left_solvable (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5) :
    Group.IsSolvable (parabolic ![K,R] (reducedSylow ![K,R] S) 0) := by
  rw [h.quintic_reducedSylow_eq hSK]
  exact h.quintic_first_solvable hSK hi

/-- Order identity retaining the entire reduced overlap. -/
theorem reduced_left_card (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5) :
    Nat.card (parabolic ![K,R] (reducedSylow ![K,R] S) 0) =
      Nat.card (commonBorel ![K,R] (reducedSylow ![K,R] S)) * 5 := by
  rw [h.quintic_reducedSylow_eq hSK]
  have hc := ((commonBorel ![K,R] S).subgroupOf (parabolic ![K,R] S 0)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (commonBorel_le_parabolic 0)).toEquiv] at hc
  change _ * (commonBorel ![K,R] S).relIndex (parabolic ![K,R] S 0) = _ at hc
  rw [h.quintic_borel_index hSK hi] at hc
  exact hc.symm

/-- A genuine model comparison transports the quintic index. Compatibility
of its two squares is not needed for this numerical consequence. -/
theorem model_left_index (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5)
    {X : Type*} [Group X] [Finite X] {P B Q : Subgroup X}
    (hBP : B ≤ P) (hBQ : B ≤ Q)
    (e : ParabolicEquiv (reducedAmalgam ![K,R] S) (ofSubgroups P B Q hBP hBQ)) :
    B.relIndex P = 5 := by
  have hl := reduced_left_card h hSK hi
  rw [Nat.card_congr e.left.toEquiv, Nat.card_congr e.middle.toEquiv] at hl
  have hc := (B.subgroupOf P).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv, hl] at hc
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := B)) hc

/-- The actual left endpoint isomorphism transports solvability. -/
theorem model_left_solvable (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5)
    {X : Type*} [Group X]
    (e : parabolic ![K,R] (reducedSylow ![K,R] S) 0 ≃* X) : Group.IsSolvable X := by
  let := reduced_left_solvable h hSK hi
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

end CFSG.Quasithin.ChapterF.Source.QuinticSolvableParabolics
