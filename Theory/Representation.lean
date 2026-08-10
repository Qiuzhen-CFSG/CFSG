module  -- shake: keep-all --deprecated_module: ignore

public import Theory.Representation.AbsolutelyIrreducible
public import Theory.Representation.Clifford
public import Theory.Representation.CompleteReducibility
public import Theory.Representation.ConjugateRep
public import Theory.Representation.CyclicQuotientExtension
public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.ExtendScalars
public import Theory.Representation.ExtraspecialFixedPoints
public import Theory.Representation.FreeBasis
public import Theory.Representation.InducedIrreducible
public import Theory.Representation.Induction
public import Theory.Representation.Isotypic
public import Theory.Representation.JacobsonDensity
public import Theory.Representation.kerRepresentation
public import Theory.Representation.KrullSchmidt
public import Theory.Representation.Maschke
public import Theory.Representation.PermutationBasisOrbits
public import Theory.Representation.RepEnd
public import Theory.Representation.RepEquiv
public import Theory.Representation.RepMap
public import Theory.Representation.ScalarDescent
public import Theory.Representation.SolvableDimension
public import Theory.Representation.SubrepresentationLattice
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Representation.Unbundled

/-!
# Representation theory infrastructure

Generic representation theory of groups over `ℂ` (and other fields): Maschke
and complete reducibility, subrepresentation lattices, representation
equivalences, induction and coinduction, Jacobson density, and the
extraspecial and solvable group representation machinery.  Character theory
built on top of this lives in `Theory/Character`.
-/
