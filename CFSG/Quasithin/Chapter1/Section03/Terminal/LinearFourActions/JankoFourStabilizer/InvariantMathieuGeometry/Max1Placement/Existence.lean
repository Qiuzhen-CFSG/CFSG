module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Reduction

/-!
# Existence of local max1 candidates: assembly interface

The proper local join and the symmetric-linear quotient obstruction are proved
in the descendant modules. `concreteCandidateExistence_of_maximal_cover` reduces
the requested candidate existence to three explicit concrete inputs: the
maximal Sylow-overgroup cover, the max2 local exclusion, and the max4 quotient
isomorphism. These inputs are not asserted here; the unconditional
`ConcreteCandidateExistenceTheorem` remains this module's assembly obligation.

Source: Aschbacher–Smith A.3.12(17), printed pp.47–48, and the proof of
1.3.9, p.514. All isomorphisms refer to actual matrix-word carriers.
-/
