module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.Assembly
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.Coefficients
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.Spanning

/-!
# Comparisons and exact source coefficients for the zero summands

The corrected tensor comparison descends through both actual orbit relations
and the sign relation. The form decomposition and spanning tests use the
literal zero summands. The coefficients on the standard triples are evaluated
from the fixed Griess form with the source normalization.

The NPlus intertwining, odd-family module comparison, full model action and
nonzero-monomial reduction are still separate prerequisites. `Assembly`
exposes only conditional transport lemmas until those inputs are constructed.
This module does not yet claim Aschbacher 29.6--29.9 in full.
-/
