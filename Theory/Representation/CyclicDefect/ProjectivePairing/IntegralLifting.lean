module

public import Theory.Representation.CyclicDefect.ProjectivePairing.IntegralLifting.CountableDescent
public import Theory.Representation.CyclicDefect.ProjectivePairing.IntegralLifting.Idempotents
public import Theory.Representation.CyclicDefect.ProjectivePairing.IntegralLifting.Transport
public import Theory.Representation.CyclicDefect.ProjectivePairing.IntegralLifting.Residue

/-!
# Preparation and assembly for integral projective lifting

Every finite-dimensional projective modular representation descends, with
its projectivity and actual intertwining equivalence, to a countable
algebraically closed subfield containing the chosen modular root. This
includes `linHom P (ρ.tprod σ)`, by the established projectivity theorem.

`IntegralLifting.assemble` combines a complete coefficient ring with a
projective residue lift and transports its reduction equivalence to the
original representation. For a finite group,
`CompleteCoefficientRing.matrixIdempotentsLift` lifts the actual group-algebra
matrix idempotents using adic completeness.
`CompleteCoefficientRing.residueProjectiveLift` realizes their projective
summands with actual reduction equivalences, and `assembleProjective` applies
them directly. The unconditional existence theorem still requires construction
of the complete coefficient ring.

Source: Feit, *The Representation Theory of Finite Groups*, I.12--13,
I.16--17, and the projective lift used in IV.3.3 (pp.145--146).
-/
