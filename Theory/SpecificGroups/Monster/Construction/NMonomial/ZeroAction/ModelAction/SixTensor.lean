module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.ModelAction.SixTensor.Cyclic

/-!
# The six oriented Parker tensor factors

This interface exports the actual signed orbit modules, marked comparisons,
cyclic relabellings and functorial isometric tensor transport obtained from
`AxisTransportData`. The preferred source slots are `(2,0)`, `(0,1)`, `(1,2)`.
All transport formulas refer to the literal ambient Parker permutations and
halfspace families.

The product representation, its trivial action on K, and covariance of the
coordinate-corrected partner equations remain separate assembly obligations.
This module does not assert the completed N-action on the glued three-slot
model or replace those obligations with an extension assumption.

Source: Aschbacher, *Sporadic Groups*, 29.7, printed pp. 156–157, using
Sections 14 and 27 for the underlying signed modules.
-/
