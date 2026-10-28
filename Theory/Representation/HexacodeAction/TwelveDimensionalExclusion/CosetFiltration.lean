module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetModule
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Interface
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.CosetIdentification
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Flag
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.FactorSpanning

/-!
# Finite certificates for the central coset module

`cosetFiltration` proves that the omega-eigenspace of the literal left-coset
module for a Sylow two-subgroup of the even hexacode cover has a filtration
with irreducible factors of dimensions three or nine over F₄.

The proof assembles the certified coordinates on that eigenspace, the invariant
flag at dimensions 0, 3, 12, 15, 18, 21, 30, 33, 42, 45, and the full
matrix-algebra spanning certificates for the literal successive quotients.
All three certificates are discharged. The resulting `CosetFiltration` is the
input to the independent degree-twelve exclusion; no absolute-irreducibility
or field-descent premise is needed.

Source: Aschbacher–Smith K.1.3, printed p.453 (PDF p.464), and the licensed
ATLAS hexacode carrier described in the witness data module.
-/

@[expose] public section
namespace Representation.Hexacode.TwelveDimensional

/-- The central Sylow coset module has an actual finite filtration whose
irreducible successive quotients all have dimension three or nine over F₄. -/
theorem cosetFiltration : CosetFiltration :=
  CosetCertificate.cosetFiltration_of_certificates
    CosetCertificate.cosetCoordinates CosetCertificate.certifiedFlagCoordinates
    CosetCertificate.factorSpanning

end Representation.Hexacode.TwelveDimensional
