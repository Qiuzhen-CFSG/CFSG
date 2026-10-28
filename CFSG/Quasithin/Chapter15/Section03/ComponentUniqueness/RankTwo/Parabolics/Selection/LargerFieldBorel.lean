module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.LargerFieldBorel.LinearRee
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.LargerFieldBorel.SplitG2
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.LargerFieldBorel.Symplectic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.LargerFieldBorel.Triality

/-!
# Assembly of the larger-field Borel containment

The source Frattini shadow supplies a solvable Sylow overgroup inside the
recognized parabolic. The concrete PSL₃, PSp₄, G₂, triality and Ree calculations
place its intersection with the normal component in the intrinsic Sylow
normalizer. All five model controls are discharged in `largerField_borel`.
Parabolic recognition remains the explicit input; model selection and the
subsequent larger-field contradiction are separate source steps.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41(2),
printed p.1138, and the first paragraph of the final proof of 15.3.35, p.1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
open LargerFieldBorel

variable {G : Type*} [Group G] [Finite G]
variable {L MI Yplus S : Subgroup G} [L.Normal]

/-- All five field-marked cases, with precisely the remaining three model
calculations explicit. The assembly owner must discharge these controls. -/
theorem largerField_borel_of_remaining_controls
    (d : Setup L MI Yplus S) (hp : QuotientParabolic L MI S)
    (hm : LargerFieldRankTwoModel (centralizerQuotientComponent L))
    (hsp : ∀ n : ℕ, 1 < n →
      ClassicalGroup.IsPSp (centralizerQuotientComponent L) 2 (2 ^ n) →
      ParabolicSolvableControl (centralizerQuotientComponent L))
    (hg2 : ∀ n : ℕ, 1 < n →
      ClassificationModels.IsG2At (centralizerQuotientComponent L) (2 ^ n) →
      ParabolicSolvableControl (centralizerQuotientComponent L))
    (htriality : ∀ n : ℕ, 1 < n →
      Triality.Standard.IsTrialityGroupAt (2 ^ n) (centralizerQuotientComponent L) →
      ParabolicSolvableControl (centralizerQuotientComponent L)) :
    Yplus.map (centralizerQuotientMap L) ≤
      sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L)) := by
  apply quotient_borel_containment d hp
  cases hm with
  | linear n hn h => exact linear_control hn h
  | symplectic n hn h => exact hsp n hn h
  | g2 n hn h => exact hg2 n hn h
  | triality n hn h => exact htriality n hn h
  | ree m hm h => exact ree_control hm h

/-- In every larger-field rank-two case on p.1139, the source Y₊ image lies
in the component's actual Borel over the supplied Sylow intersection.
The source action is needed to select the model, but no additional action
hypothesis is required once this model and the parabolic are recognized. -/
theorem largerField_borel
    (d : Setup L MI Yplus S) (hp : QuotientParabolic L MI S)
    (hm : LargerFieldRankTwoModel (centralizerQuotientComponent L)) :
    Yplus.map (centralizerQuotientMap L) ≤
      sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L)) := by
  exact largerField_borel_of_remaining_controls d hp hm
    (fun _ hn h => symplectic_control hn h)
    (fun _ hn h => g2_control hn h)
    (fun _ hn h => triality_control hn h)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
