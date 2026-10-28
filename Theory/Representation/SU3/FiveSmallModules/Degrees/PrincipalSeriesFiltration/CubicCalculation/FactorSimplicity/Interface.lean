module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.FactorSimplicity.Certificates
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Realization

/-!
# The remaining finite certificates for the chosen cubic flag

This contract specializes the matrix-certificate interface to the actual
`modelCoordinates` and proved `matrix_relations` used by `model_flags`.
Its two density assertions and coordinate-action identities remain to be
constructed. There is no irreducibility conclusion among its fields.

A certificate producer should import this interface, leaving the final
simplicity assembly free to import that producer without an import cycle.
Source motivation: Guralnick–Malle, Proposition 4.3, p.10;
Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.FactorSimplicity
universe v

/-- The finite arithmetic and quotient coordinates still required for the
actual flag, over every original finite characteristic-two coefficient field. -/
def ModelCertificates : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1),
    Nonempty (Certificate (ModelFlag.modelCoordinates χ hne hcube) ModelFlag.matrix_relations)

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.FactorSimplicity
