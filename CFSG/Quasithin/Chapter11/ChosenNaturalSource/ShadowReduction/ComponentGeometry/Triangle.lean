module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.WeakClosure
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RootSpan

/-!
# Initial source steps in the field-four triangle exclusion

The weak-closure normalizer bound selects a conjugate of the original V
inside the actual second radical. Its action on a marked swapped module
has rank at least four. The symplectic root-preimage centralizers span that
module, and their index bound together with r(G,V)>4 proves that it
normalizes the selected conjugate.

These results retain the original chosen flag and literal subgroup maps.
The Reselection and RankComparison extensions construct the swapped natural
marking and compare it with the G₂ action. The completed triangle exclusion
feeds `Radical.ofFlag_refinement_and_bounds_of_preceding_sources`, re-exported
by ComponentGeometry, which supplies 11.4.1(2–3) under the explicit earlier
source inputs. This module provides the initial root-span ingredients.
Source: Aschbacher--Smith, 11.4.1, printed pp.775--776.
-/
