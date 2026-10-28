module

public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Parameters
public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Transport
public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.QuotientAction

/-!
# Local octad structure

The local action is the literal restriction of the constructed centralizer
representation to the existing octad summand. Its signed short lifts,
Griess inclusion, and source forms use the fixed carrier without any new
model or normalization. The coordinate permutation transports the blocks,
and its stabilizer has the literal restricted block representation. The
local action also descends to the actual subgroup `N1Image` of `N/K`. The
three source parameter transformations are valid and respect both signs
and complements, including the required half-weight parity identity.

Source: Aschbacher, *Sporadic Groups*, Lemmas 29.12–29.13, pp. 160–161.
The conjugation formulas and the fixed-space, kernel, and quotient clauses
of 29.13 are separate remaining results, not assertions of this module.
-/
