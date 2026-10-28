module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Planes
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.FixedPoints
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors

/-!
# Certified coordinates for the literal Held pair representatives

`candidateOddEquiv` constructs all four actual planes unconditionally, with
explicit generator formulas. For j=1, the two marked axes cannot be exchanged
by any ambient permutation. The inner-actor calculations identify the diagonal
image once the fixed representative's normalizer equality is supplied. Genuine
ambient-normalizer actors at j=0 induce a quarter-turn and its inverse. The
chapter adapter discharges the normalizer premise and assembles the exact full
images, including every extending actor.

Source context: GLS3 Table 5.3p; Aschbacher–Smith, printed pp.509–511.
-/
