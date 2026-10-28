module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank.Reverse
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry.Reverse

/-!
# Both weak-closure bounds for the doubled natural branches

The first-stage offender has image rank at least n−1. Degree five is
excluded by its existing core argument. In degree four the low-rank pure
plane and the high-rank core-faithfulness arguments exclude both remaining
possibilities. The compatible action model is constructed on the literal
automizer; no model or local contradiction premise remains.

The second-stage bound is already proved by the corank-three core estimate.
The source inputs (pure intersections, positive w, and the two r bounds)
remain explicit for final assembly by qt-d-1222-double-natural.
Source: Aschbacher--Smith, 12.1.8 and 12.1.10, pp.792--794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {n : ℕ} (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- The complete rank n−1 offender exclusion for both source degrees. -/
theorem first_low_rank_false (M : B.MarkedAutomizerModel)
    (hp : B.PureIntersectionCentralizes) {g : G}
    (C : ConjugateConfiguration (componentOrbit V (T : Subgroup G)) g 1 n)
    (hr : rank (inducedAutomizer (componentOrbit V (T : Subgroup G))
      (offenderNormalizer (componentOrbit V (T : Subgroup G)) g)) = n-1) : False := by
  rcases B.degree with hn | hn
  · subst n
    exact four_first_low_rank_false B M hp C hr
  · subst n
    exact five_first_low_rank_false B M hp C hr

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
include h D

/-- The degree-four conditional implication of 12.1.8. -/
theorem doubledFour_globalW_gt_one_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    B.PureIntersectionCentralizes →
    0 < globalW (componentOrbit V (T : Subgroup G)) T →
    (4 : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
    1 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro hp hw hr
  let M := D.doubled_markedAutomizerModel h B
  by_contra hf
  obtain ⟨g,hg,he,C,_⟩ :=
    D.doubled_first_configuration_of_many h hmany B hp hw hr hf
  by_cases hI : 4 ≤ rank (inducedAutomizer (componentOrbit V (T : Subgroup G))
      (offenderNormalizer (componentOrbit V (T : Subgroup G)) g))
  · exact four_first_high_rank_false B M hp C hg he hr hI
  · apply LowRank.four_first_low_rank_false B M hp C
    have hl := C.rank_lower
    omega

/-- Both conditional first-stage weak-closure bounds, with all local
action-model and offender premises discharged. -/
theorem doubled_globalW_gt_one_of_many {n : ℕ}
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    B.PureIntersectionCentralizes →
    0 < globalW (componentOrbit V (T : Subgroup G)) T →
    (n : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
    1 < globalW (componentOrbit V (T : Subgroup G)) T := by
  rcases B.degree with hn | hn
  · subst n
    exact D.doubledFour_globalW_gt_one_of_many h hmany B
  · subst n
    exact D.doubledFive_globalW_gt_one_of_many h hmany B

/-- The two-stage application used by the final doubled-branch exclusion. -/
theorem doubled_weakClosure_bounds_of_many {n : ℕ}
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    B.PureIntersectionCentralizes →
    0 < globalW (componentOrbit V (T : Subgroup G)) T →
    (n : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
    1 < globalW (componentOrbit V (T : Subgroup G)) T ∧
      (((n + 2 : ℕ) : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
        2 < globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hp hw hr
  have hfirst := D.doubled_globalW_gt_one_of_many h hmany B hp hw hr
  exact ⟨hfirst, D.doubled_globalW_gt_two_of_many h hmany B hfirst⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
