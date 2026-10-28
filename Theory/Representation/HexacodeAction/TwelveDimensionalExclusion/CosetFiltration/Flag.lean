module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Interface
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Flag.MatrixChecks
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Flag.Construction

/-!
# The nine-stage central coset flag and its literal quotient coordinates

The certified basis inverse and generator equations transport the coordinate
prefixes at cuts 0, 3, 12, 15, 18, 21, 30, 33, 42, 45 to invariant subspaces of
the published word representation. Each successive block projection identifies
the literal quotient with its specified coordinate space, intertwining both
free generators with the unchanged `factorMatrix`.

This proves the flag ingredient for Aschbacher–Smith K.1.3, printed p.453 /
PDF p.464. The final application retains the independently owned identification
with the actual coset module and the matrix-algebra spanning certificate;
it asserts neither of those inputs without proof.
-/

@[expose] public section
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate

/-- The actual invariant subspaces and equivariant coordinates on their
literal successive quotients, obtained from the published basis. -/
noncomputable def certifiedFlagCoordinates : FlagCoordinates :=
  Flag.flagCoordinates Flag.basisCoordinates Flag.basisCoordinates_generator Flag.upper

/-- The fixed 45-dimensional word representation admits the full nine-stage
flag with the prescribed generator matrices on every successive quotient. -/
theorem exists_flagCoordinates : Nonempty FlagCoordinates :=
  ⟨certifiedFlagCoordinates⟩

/-- The flag premise of `cosetFiltration_of_certificates` is now discharged.
The coset identification and factor spanning remain independent inputs for
the source-theorem assembly owner. -/
theorem cosetFiltration_of_coordinates_and_spanning (C : CosetCoordinates)
    (hspan : FactorSpanning) : CosetFiltration :=
  cosetFiltration_of_certificates C certifiedFlagCoordinates hspan

end Representation.Hexacode.TwelveDimensional.CosetCertificate
