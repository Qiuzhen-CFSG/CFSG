module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.FactorSimplicity.Interface
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.DensityCertificates

/-!
# Simplicity of the actual cubic principal-series flag

The checked quotient comparisons and scalar-extension argument apply finite
matrix-density certificates to the exact stages chosen by `model_flags`.
Both end quotients use the same image certificate; the middle quotient uses
its own degree-84 certificate. The resulting filtration retains the original
coefficient field and the original nontrivial cubic Borel character.

The completed `ModelFlag.FactorCoordinates.modelCertificates` discharges
the matrix identities, quotient-action comparisons and full matrix-algebra
density over the four-element coefficient field. The constructed evaluation
at the original character's cubic scalar preserves density over the original
field, without an embedding premise. Thus `model_flags_simple` proves
simplicity of all three literal quotients, and `model_filtrations` supplies
the model-filtration input for the general matrix-field transport.

This proves the cubic principal-series calculation used by the small-module
argument. The cited small-module classification and exclusion have separate
assembly owners.

Source motivation: Guralnick–Malle, Proposition 4.3, p.10;
Aschbacher–Smith K.2, printed p.453.
-/

public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
universe v

/-- Application to the literal chosen flag, keeping the finite certificate explicit. -/
theorem model_flags_simple_of_certificate
    (K : Type v) [Field K] [Finite K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1)
    (C : FactorSimplicity.Certificate (ModelFlag.modelCoordinates χ hne hcube)
      ModelFlag.matrix_relations) : (model_flags K χ hne hcube).Simple :=
  C.simple

/-- Uniform certificates give simplicity for every original field and character. -/
theorem model_flags_simple_of_certificates (hc : FactorSimplicity.ModelCertificates.{v}) :
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1),
      (model_flags K χ hne hcube).Simple := by
  intro K _ _ _ χ hne hcube
  obtain ⟨C⟩ := hc K χ hne hcube
  exact model_flags_simple_of_certificate K χ hne hcube C

/-- Actual application to the model-filtration consumer; only finite certificates remain. -/
theorem model_filtrations_of_certificates (hc : FactorSimplicity.ModelCertificates.{v}) :
    ModelFiltrations.{v} :=
  model_filtrations_of_simple_flags model_flags (model_flags_simple_of_certificates hc)

/-- All three literal successive quotients of the chosen cubic flag are simple,
over every original finite characteristic-two coefficient field. -/
theorem model_flags_simple
    (K : Type v) [Field K] [Finite K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1) :
    (model_flags K χ hne hcube).Simple :=
  model_flags_simple_of_certificates ModelFlag.FactorCoordinates.modelCertificates K χ hne hcube

/-- The completed simple flag gives the required degree filtration on the
original induced representation, with no remaining certificate premises. -/
theorem model_filtrations : ModelFiltrations.{v} :=
  model_filtrations_of_simple_flags model_flags model_flags_simple

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
