module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup.Data
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.Certificate

/-!
# Kernel-checked finite matrix identities

These checks use the explicit pair arithmetic of F₂₅. They certify determinant
one, preservation of the antidiagonal Hermitian form, the root-coordinate
conditions, all 252 right-action transitions, and their retained cubic
coefficients. They do not assert distinctness of cosets or group generation.
The representative late-row calculation was measured before expanding the
finite checks. No native evaluator or external computation proves an identity.

Data source: `Coordinates/source/upper_group_data.json`; mathematical use:
Guralnick–Malle Proposition 4.3, p.10, and Aschbacher–Smith K.2, p.453.
-/

public section
open BenderSuzuki.MatrixGroups
open HermitianForm.InvolutionConjugateBounds.Five.Embedding
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup

theorem generator_det (a : Fin 2) : (rawGenerator a).det = 1 := by
  revert a
  decide +kernel

theorem generator_unitary (a : Fin 2) :
    fieldForm.conjTranspose (rawGenerator a) * fieldForm.form * rawGenerator a =
      fieldForm.form := by
  revert a
  decide +kernel

theorem representative_det (i : Fin 126) : (rawRepresentative i).det = 1 := by
  revert i
  decide +kernel

theorem representative_unitary (i : Fin 126) :
    fieldForm.conjTranspose (rawRepresentative i) * fieldForm.form * rawRepresentative i =
      fieldForm.form := by
  revert i
  decide +kernel

theorem root_condition (a : Fin 2) (i : Fin 126) :
    (rootValues a i).2 + F25.conjugation (rootValues a i).2 +
      (rootValues a i).1 * F25.conjugation (rootValues a i).1 = 0 := by
  revert a i
  decide +kernel

theorem raw_transition (a : Fin 2) (i : Fin 126) :
    rawRepresentative i * rawGenerator a =
      rootMatrix (rootValues a i).1 (rootValues a i).2 *
      torusMatrix (exponent a i) * rawRepresentative (generatorTarget a i) := by
  revert a i
  decide +kernel

theorem coefficient (a : Fin 2) (i : Fin 126) :
    decode (generatorCode a i) = (QuadraticAlgebra.omega : CoefficientField) ^ exponent a i := by
  revert a i
  decide +kernel

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup
