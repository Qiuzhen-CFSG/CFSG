module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Normalizer
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Candidates
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Transport

/-!
# Literal Held pairs, coordinates and restriction-image transport

The candidate orders and finite subgroup cover support simultaneous pair
conjugacy. The representative modules supply actual plane equivalences,
inner-action certificates and outer actors. `Normalizer` bounds the full
extending image by the monomial group once its inner image is diagonal.
`Transport` carries full and inner restriction images through the same
ambient equivalence; the chapter adapter assembles the placed-pair result.

Sources: Aschbacher–Smith, printed pp.509–511; GLS3 Table 5.3p.
-/
