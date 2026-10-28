module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Filtration
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.BranchInputs
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.Model

/-!
# Spectral certificates for the two canonical principal series

The inputs below concern actual simple-factor filtrations of the literal
induced modules over the fixed matrix field GF(25). Each retains the original
coefficient field. The trivial and nontrivial cubic branches can be checked
independently using their existing flags and quotient coordinates.

No spectrum is required of a factor larger than 21. In particular, the
104- and 84-dimensional factors need no further matrix calculation. These
contracts do not assert that the small-factor spectra have been calculated.
The assembly owner transports these filtrations to every permitted form and
extracts the spectra of all irreducible subquotients.

Source application: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open Polynomial
namespace Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors
open Degrees.CubicCalculation
universe v

/-- The required integer multiplicities, restricted to the small factors. -/
def SmallSpectrum (K : Type*) [Field K] (d : ℕ) (p : K[X]) : Prop :=
  d ≤ 21 → (d = 1 ∧ p = X - C 1) ∨
    ((d = 20 ∨ d = 21) ∧ p = sevenSpectrum K d)

/-- A spectral filtration of the actual untwisted canonical principal series. -/
def TrivialModelSpectralFiltrations : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (x : standardGroup modelForm), orderOf x = 7 →
    FactorPolynomialFiltration (SmallSpectrum K) x
      (ind (standardBorel modelForm).subtype
        (scalarCharacter (1 : standardBorel modelForm →* Kˣ)))

/-- Both nontrivial cubic characters over every original coefficient field,
with spectra on actual simple quotients of the canonical induced module. -/
def CubicModelSpectralFiltrations : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ),
    χ ≠ 1 → (∀ b, χ b ^ 3 = 1) →
    ∀ (x : standardGroup modelForm), orderOf x = 7 →
      FactorPolynomialFiltration (SmallSpectrum K) x
        (ind (standardBorel modelForm).subtype (scalarCharacter χ))

end Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors
