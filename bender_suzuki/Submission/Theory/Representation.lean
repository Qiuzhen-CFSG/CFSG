module  -- shake: keep-all --deprecated_module: ignore

public import Submission.Theory.Representation.AbsolutelyIrreducible
public import Submission.Theory.Representation.Clifford
public import Submission.Theory.Representation.CompleteReducibility
public import Submission.Theory.Representation.ConjugateRep
public import Submission.Theory.Representation.CyclicQuotientExtension
public import Submission.Theory.Representation.ElementaryAbelianAction
public import Submission.Theory.Representation.ExtendScalars
public import Submission.Theory.Representation.ExtraspecialFixedPoints
public import Submission.Theory.Representation.FreeBasis
public import Submission.Theory.Representation.InducedIrreducible
public import Submission.Theory.Representation.Induction
public import Submission.Theory.Representation.Isotypic
public import Submission.Theory.Representation.JacobsonDensity
public import Submission.Theory.Representation.kerRepresentation
public import Submission.Theory.Representation.KrullSchmidt
public import Submission.Theory.Representation.Maschke
public import Submission.Theory.Representation.PermutationBasisOrbits
public import Submission.Theory.Representation.RepEnd
public import Submission.Theory.Representation.RepEquiv
public import Submission.Theory.Representation.RepMap
public import Submission.Theory.Representation.ScalarDescent
public import Submission.Theory.Representation.SolvableDimension
public import Submission.Theory.Representation.SubrepresentationLattice
public import Submission.Theory.Representation.TwoDimensionalOddOrder
public import Submission.Theory.Representation.Unbundled

/-!
# Representation theory infrastructure

Generic representation theory of groups over `ℂ` (and other fields): Maschke
and complete reducibility, subrepresentation lattices, representation
equivalences, induction and coinduction, Jacobson density, and the
extraspecial and solvable group representation machinery.  Character theory
built on top of this lives in `Theory/Character`.
-/
