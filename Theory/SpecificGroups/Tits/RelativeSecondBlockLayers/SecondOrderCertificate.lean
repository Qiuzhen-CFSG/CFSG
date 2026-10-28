module

public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers.SecondOrderCertificate.Rows0To2
public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers.SecondOrderCertificate.Rows3To5
public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers.SecondOrderCertificate.Rows6To8
import Mathlib.Tactic.FinCases

/-!
# The complete three-coset transition certificate

The three independently compiled row modules check all forward transitions
for the nine generators. The inverse coset permutation is checked in `Data`;
`SecondOrder` derives inverse word transitions by group algebra.
Source and table conventions: Parrott (1972), p.683; see `Data`.
-/

@[expose] public section
namespace Tits.RelativeSecondBlockLayers.SecondOrder

theorem step (a : Fin 9) (i : Fin 3) :
    rep i * generator a = atlas1600SylowTwoNormalForm (factor a i) * rep (dest a i) := by
  fin_cases a
  · exact step_0 i
  · exact step_1 i
  · exact step_2 i
  · exact step_3 i
  · exact step_4 i
  · exact step_5 i
  · exact step_6 i
  · exact step_7 i
  · exact step_8 i
end Tits.RelativeSecondBlockLayers.SecondOrder
