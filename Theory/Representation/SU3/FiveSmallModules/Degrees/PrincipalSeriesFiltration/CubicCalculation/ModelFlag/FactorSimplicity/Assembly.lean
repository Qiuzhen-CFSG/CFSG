module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Coordinates
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.FactorSimplicity.Interface

/-!
# Applying the concrete quotient coordinates to the cubic flag

The checked coordinate maps and generator formulas discharge every field of
the existing factor certificate except the two matrix-algebra density claims.
This module records their exact consumer over each original field and character.
Both density premises remain explicit until the independent finite proofs are
supplied. In particular, this is not an unconditional simplicity theorem.

Source motivation: Guralnick–Malle Proposition 4.3, p.10;
Aschbacher–Smith K.2, p.453.
-/

@[expose] public noncomputable section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates
universe v
open CubicCalculation.FactorSimplicity

/-- All actual coordinate and action fields, with only the two density proofs left. -/
def certificateOfDensity {K : Type v} [Field K] [CharP K 2]
    {χ : standardBorel modelForm →* Kˣ} (c : Coordinates χ) (h : MatrixRelations.{v})
    (hi : MatrixDensity imageMatrices) (hm : MatrixDensity middleMatrices) :
    CubicCalculation.FactorSimplicity.Certificate c h where
  imageMatrices := imageMatrices
  middleMatrices := middleMatrices
  imageCoordinates := imageCoordinates c.z c.quadratic
  middleCoordinates := middleCoordinates c h
  image_action := image_action c.z c.quadratic h
  middle_action := middle_action c h
  image_density := hi
  middle_density := hm

/-- Uniform application to the actual coordinates chosen by `model_flags`. -/
theorem modelCertificates_of_density
    (hi : MatrixDensity imageMatrices) (hm : MatrixDensity middleMatrices) :
    ModelCertificates.{v} := by
  intro K _ _ _ χ hne hcube
  exact ⟨certificateOfDensity (modelCoordinates χ hne hcube) matrix_relations hi hm⟩

/-- Concrete consumer application, keeping precisely the two finite obligations explicit. -/
theorem model_flags_simple_of_density
    (hi : MatrixDensity imageMatrices) (hm : MatrixDensity middleMatrices)
    (K : Type v) [Field K] [Finite K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1) :
    (model_flags K χ hne hcube).Simple :=
  (certificateOfDensity (modelCoordinates χ hne hcube) matrix_relations hi hm).simple

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates
