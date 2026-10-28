module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Pairing
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.PairVectors
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure

/-!
# The native M22 module constructions for H.13--H.16

The code is the existing native hyperplane. The cocode is the actual quotient
of the eleven-dimensional even cocode by the class of the distinguished pair
at coordinates 0 and 9. Both dimensions are ten, and the coordinate dot product
is a genuine equivariant duality. These actions extend to the literal setwise
pair stabilizer in M24 and restrict to the existing native M22 action.

The geometry uses an explicit conjugate of the standard sextet with both
points in one tetrad. The local kernels are defined as relative two-cores.
The construction does not identify the setwise stabilizer with `MulAut M22`,
assert absolute irreducibility, or assert the chief flags and local calculations
of H.15--H.16; those require additional mathematical proofs.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), H.13.1,
printed p.395; setup of H.14, p.396; H.15--H.16, pp.398--404.
-/
