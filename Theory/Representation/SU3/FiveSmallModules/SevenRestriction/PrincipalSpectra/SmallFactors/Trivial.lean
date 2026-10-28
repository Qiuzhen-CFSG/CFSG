module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Trivial.Assembly
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Trivial.Quotient

/-!
# The untwisted canonical principal-series seven-spectrum

The actual coset flag has simple factors of dimensions 1, 104, 20 and 1.
Both end factors have the identity action. An explicit matrix certificate
on the literal twenty-dimensional quotient gives three copies of each
nontrivial seventh root and two fixed roots over every original coefficient
field. The induction/coset equivalence therefore gives the requested spectral
filtration of the literal trivial-character induced module. The large factor
requires no polynomial condition.

Source application: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

namespace Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors
universe v
/-- The literal canonical trivial principal series has a simple spectral filtration
of successive degrees 1, 104, 20 and 1 over every finite characteristic-two field. -/
theorem trivial_model_spectral_filtrations : TrivialModelSpectralFiltrations.{v} := by
  intro K _ _ _ x hx
  change FactorPolynomialFiltration (SmallSpectrum K) x
    (ind Degrees.TrivialCalculation.canonicalBorel.subtype
      (Degrees.scalarCharacter (1 : Degrees.TrivialCalculation.canonicalBorel →* Kˣ)))
  exact Trivial.induction_filtration_of_coordinates (Trivial.quotientCoordinates K) x
    (Trivial.upper_charpoly x hx)
end Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors
