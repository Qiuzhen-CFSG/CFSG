module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Reduction
public import Theory.GroupAction.NormalizerGeneratingFixer.MaximalOvergroups
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
/-!
# From proper-overgroup bounds and a parabolic pair to a full fixer bound

For a finite simple perfect group the center is trivial, so the published
proper Sylow-overgroup bound makes every proper Sylow overgroup of
characteristic two. Two distinct maximal overgroups of a common Sylow group
then give the full automorphism fixer bound by the normalizer displacement
argument. The existence of that pair remains an explicit geometric premise.

This is a conditional assembly step for Aschbacher–Smith, B.1.13, printed
pp.73–74 of `refs/quasithin.pdf`, rather than a family classification.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupAction.NormalizerGeneratingFixer
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers
variable {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] [Group.IsPerfect X]

/-- Local characteristic two and two distinct maximal Sylow overgroups control the entire fixer. -/
theorem fixer_of_properFitting_of_two_maximals
    (hfit : ProperSylowFittingBound X) (hgeom : HasTwoMaximalOvergroups 2 X) :
    SylowFixerIsTwoGroup X := by
  have hZ : center X = ⊥ := by
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp h)).elim
  obtain ⟨S, M, N, hM, hN, hne, hSM, hSN⟩ := hgeom
  have hc (P : Subgroup X) (hSP : (S : Subgroup X) ≤ P) (hP : P ≠ ⊤) :
      centralizer (pCore 2 P : Set P) ≤ pCore 2 P := by
    have h := hfit S P hSP hP
    have hbound : generalizedFitting P ≤ pCore 2 P := by simpa [hZ] using h
    exact (centralizer_le hbound).trans ((centralizer_generalizedFitting_le P).trans hbound)
  exact sylow_fixer_of_two_maximals S M N hM hN hne hSM hSN
    (hc M hSM hM.ne_top) (hc N hSN hN.ne_top)
end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers
