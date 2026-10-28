module

public import Theory.Representation.PSL3Two.FanoLocalStructure.Basic
public import Theory.Representation.PSL3Two.FanoLocalStructure.SelfDual
public import Theory.Representation.PSL3Two.FanoLocalStructure.Orbits
public import Theory.Representation.PSL3Two.FanoLocalStructure.ParabolicSpaces

/-!
# Local geometry of the binary Fano core

The four literal nonzero families in the six-dimensional point core are the
point complements, line complements, two-point subsets, and complements of
bases. They are precisely the four group orbits, of sizes 7, 7, 21, and 28.
The module also supplies the concurrent-line addition identity, an equivariant
self-duality, and all the marked Sylow and parabolic fixed-space calculations.
Both intrinsic parabolic two-cores have fixed and commutator spaces of dimension
three. For every Sylow three-subgroup of the line parabolic, its fixed natural
point determines the two generators of its fixed space in the core.

Point and basis transitivity identify the orbits, with kernel-checked finite
certificates proving the counts and local fixed spaces. The invariant perfect
pairing gives the commutator dimensions. Evaluation outside the marked line
and the concurrent-line geometry prove the two directional commutator
assertions; a point outside three chosen points detects the nonzero sum of
their complements.

The constituent modules prove all of H.5.2, H.5.3(3–4), and H.5.4 for the
actual marked Fano action. In H.5.2(1), the two initial lines are distinct,
as required for the source's third concurrent line to be defined.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.385–386 (PDF pp.396–397).
-/
