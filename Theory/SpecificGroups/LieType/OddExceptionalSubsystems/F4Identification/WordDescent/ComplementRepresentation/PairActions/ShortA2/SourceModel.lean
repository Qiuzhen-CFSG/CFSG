module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.Model
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.Transport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.Coordinates
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.SourceModel.Transport

/-!
# The block-action route to the short F4 matrix model

`SourceBlocks.action` is a proved faithful action of full SL3 on a
52-dimensional space of concrete matrix blocks, including the full diagonal
lattice in characteristic three. `SourceBlocks.sourceModelOfChart` and
`SourceBlocks.pairLiftOfChart` connect a marked change of basis to the actual
F4 cover and its literal two-node subgroup.

The concrete chart and its `SourceBlocks.Intertwines` proof remain to be
constructed. Consequently this module currently reexports conditional
assembly, and does not assert the requested unconditional `sourceModel`.
Final assembly belongs here once those coordinate identities are proved.

Source: GLS3 §2.6.2 and Aschbacher--Smith A.2.17, printed p.39.
-/
