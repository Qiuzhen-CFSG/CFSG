module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar.LowRank
public import Theory.GroupAction.SylowFixerLocalGeneration
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# From proper Sylow overgroups to the B.1.13 fixer bound

For a finite simple perfect group, the proper-overgroup Fitting bound gives
characteristic two for every proper Sylow overgroup. Two such overgroups that
generate the group yield a two-group pointwise Sylow fixer by the local
normalizer argument. This applies to every automorphism, including diagram
automorphisms. The characteristic-two bound and generating overgroups remain
explicit inputs until the model calculations are supplied.

Source: Aschbacher–Smith B.1.13, printed pp.73–74 of `refs/quasithin.pdf`.
The split orthogonal application preserves the elementary scalar quotient.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] [Group.IsPerfect G]

private theorem characteristicTwo_of_properSylowFittingBound
    (hbound : ProperSylowFittingBound G) (S : Sylow 2 G)
    (P : Subgroup G) (hSP : (S : Subgroup G) ≤ P) (hP : P ≠ ⊤) :
    centralizer (pCore 2 P : Set P) ≤ pCore 2 P := by
  have hZ : center G = ⊥ := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative G (center_eq_top_iff.mp h)).elim
  have hF : generalizedFitting P ≤ pCore 2 P := by
    simpa only [hZ, bot_subgroupOf, sup_bot_eq] using hbound S P hSP hP
  exact (centralizer_le hF).trans ((centralizer_generalizedFitting_le P).trans hF)

/-- The two independent local inputs imply the entire Sylow fixer bound.
No automorphism coverage or assumption on actor orders is required. -/
theorem fixer_of_properSylowFittingBound_of_generating_pairs
    (hbound : ProperSylowFittingBound G)
    (hpair : ∀ S : Sylow 2 G, ∃ P R : Subgroup G,
      (S : Subgroup G) ≤ P ∧ (S : Subgroup G) ≤ R ∧
      P ≠ ⊤ ∧ R ≠ ⊤ ∧ P ⊔ R = ⊤) : SylowFixerIsTwoGroup G := by
  intro S
  exact Theory.GroupAction.SylowFixerLocalGeneration.isPGroup_fixingSubgroup_of_generating_overgroups S
    (characteristicTwo_of_properSylowFittingBound hbound S) (hpair S)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar
