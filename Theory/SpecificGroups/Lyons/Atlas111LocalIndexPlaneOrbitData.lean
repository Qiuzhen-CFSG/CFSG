module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbitData.BatchChecks
public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbitData.PivotPatterns
public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbitData.TreeChecks

/-!
# Data interfaces for the exact Lyons plane tree

The imported modules certify the packed root, batched canonical-digit and
reduced-basis shape checks, bit-mask shape checks, certified pivot masks, tree-fold checking, and exact
matrix separation by sorted encodings.
The complete 8,835,156-node table and its closed certificates have not yet been
supplied; this module does not assert the existence of that table or the
unconditional orbit bound.

Encoding and source conventions are documented in
`Atlas111PlaneOrbitSource/README.md` and the `Encoding` module.
-/
