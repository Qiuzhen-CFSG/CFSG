module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Density21
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Density84

/-!
# Completed density certificates for the literal cubic factors

The checked degree-21 and degree-84 matrix algebras supply both remaining
density fields of the concrete quotient certificate. Evaluation at the supplied
cubic scalar transports these results to every characteristic-two coefficient
field, without a separate embedding premise. The image coordinates are x ↦ Lx
with inverse y ↦ Uy; the literal middle quotient has coordinates [x] ↦ Sx
with inverse y ↦ [Wy]. Their action formulas are proved in `Coordinates`.

Applying this certificate to the actual `model_flags` proves simplicity of all
three successive quotients. The first and last use the same image action;
the middle uses precisely ker N / range N. `modelCertificates` is the uniform
input for the separate `CubicCalculation.FactorSimplicity` assembly.

This is the cubic principal-series calculation used in the small-module
argument, not the whole classification of small modules.
Source motivation: Guralnick–Malle Proposition 4.3, p.10;
Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public noncomputable section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates
open CubicCalculation.FactorSimplicity
universe v

/-- Density of the exact image matrices over every supplied cubic scalar. -/
theorem image_density_evaluate {K : Type v} [Field K] [CharP K 2]
    (z : K) (hz : z ^ 2 + z + 1 = 0) :
    MatrixDensity (fun a => (imageMatrices a).map (evaluate z hz)) :=
  density_evaluate z hz imageMatrices image_density

/-- Density of the literal middle-quotient matrices after cubic evaluation. -/
theorem middle_density_evaluate {K : Type v} [Field K] [CharP K 2]
    (z : K) (hz : z ^ 2 + z + 1 = 0) :
    MatrixDensity (fun a => (middleMatrices a).map (evaluate z hz)) :=
  density_evaluate z hz middleMatrices middle_density

/-- The complete certificate for any actual induction coordinates, using the
proved nilpotent relations and both proved coefficient-field density results. -/
def certificate {K : Type v} [Field K] [CharP K 2]
    {χ : standardBorel modelForm →* Kˣ} (c : Coordinates χ) :
    CubicCalculation.FactorSimplicity.Certificate c matrix_relations :=
  certificateOfDensity c matrix_relations image_density middle_density

/-- Uniform complete certificates for the original field and cubic character. -/
theorem modelCertificates : ModelCertificates.{v} :=
  modelCertificates_of_density image_density middle_density

/-- Actual consumer: all three literal successive quotients of the chosen
principal-series flag are simple, with no remaining certificate premises. -/
theorem model_flags_simple
    (K : Type v) [Field K] [Finite K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1) :
    (model_flags K χ hne hcube).Simple :=
  (certificate (modelCoordinates χ hne hcube)).simple

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates
