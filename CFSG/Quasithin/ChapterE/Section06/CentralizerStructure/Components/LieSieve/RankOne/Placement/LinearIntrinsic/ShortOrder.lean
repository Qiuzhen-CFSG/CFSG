module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.LinearIntrinsic.Contracts
public import CFSG.Quasithin.ChapterC.Section01.SolvableShortAbelianCore

/-!
# The short-group order input for the binary linear Borel exclusion

The literal short-group hypotheses, solvability and an abelian two-core
imply order twelve. This discharges the numerical Chapter C input while
leaving the Borel subgroup calculation with its independent owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–13,
printed pp.123–125, applied in E.6.8, printed pp.247–248.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne

/-- The solvable short-group numerical input, with no additional premises. -/
theorem linearShortOrderInput : LinearShortOrderInput := by
  intro A _ _ _ _ h
  exact h.card_eq_twelve_of_solvable_of_abelian_core

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
