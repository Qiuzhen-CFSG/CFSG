module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.ClosedRoots
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.TorusCoordinates
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.TorusAction
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.Parametrizations
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.Realization

/-!
# Regular Spin D4 root curves and their conditional root realization

The anchored root-point subgroups are closed and have genuine normalized
one-parameter algebraic isomorphisms. The forward maps are explicit Clifford
curves; the inverse maps recover the parameter through the regular Spin
cover. Their inclusion and Omega compatibility preserve the exact root points.

For any closed maximal torus with an actual algebraic simple-coroot coordinate
isomorphism, `rootData_isRealization` proves the exhaustive D4 realization.
The based, root-system and root-addition comparisons use the standard base,
with vertex 1 central. The cocharacters equal the normalized source coroot
words. The torus and its coordinate isomorphism are the only geometric inputs;
their independent construction remains with the torus producer.

Source: GLS3, §§1.9–1.14 (`refs/KGroup/GLS3/Chapter1.tex`).
-/
