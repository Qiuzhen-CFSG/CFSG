module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Largest1792.Coordinates
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.NonzeroQuotient

/-!
# Native 1792 quotient from the saved finite identities

The two generator identities of the saved quotient remain explicit. Their
transposes yield the prescribed column-action matrices.
One nonzero entry and the proved target density give surjectivity; the native
generator closure then gives an action on the quotient by the invariant kernel.
No presentation comparison is used. Sources: James (1973), GM02 Proposition 5.1,
Aschbacher–Smith K.4 p.457; witness attribution in Largest1792/source/README.md.
-/

public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Largest1792
open Degree220Pair.NativeActions.CertificatePacked TensorCoordinates

theorem projection_ne_zero : Matrix.toLin' projection ≠ 0 := by
  intro h
  have hm : projection = 0 := by
    simpa only [LinearMap.toMatrix'_toLin', map_zero] using congrArg LinearMap.toMatrix' h
  have hv : projection 0 0 = 1 := by decide +kernel
  have he := congrArg (fun M : Matrix (Fin 1792) (Fin 2420) (ZMod 2) => M 0 0) hm
  rw [hv, Matrix.zero_apply] at he
  exact one_ne_zero he

theorem projection_first
    (hA : matrix 2420 2420 ambientA * embedding =
      embedding * Degrees12421792.Data1792.first) :
    (Matrix.toLin' projection).comp (action2420 Degree220Pair.generatorA) =
      (Matrix.toLin' Degrees12421792.Data1792.first.transpose).comp (Matrix.toLin' projection) := by
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  have h := congrArg Matrix.transpose hA
  simpa only [projection, Matrix.transpose_mul, ← native_matrix_A,
    Matrix.transpose_transpose] using h

theorem projection_second
    (hB : matrix 2420 2420 ambientB * embedding =
      embedding * Degrees12421792.Data1792.second) :
    (Matrix.toLin' projection).comp (action2420 Degree220Pair.generatorB) =
      (Matrix.toLin' Degrees12421792.Data1792.second.transpose).comp (Matrix.toLin' projection) := by
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  have h := congrArg Matrix.transpose hB
  simpa only [projection, Matrix.transpose_mul, ← native_matrix_B,
    Matrix.transpose_transpose] using h

/-- The two saved finite identities give an action on native Witt-design M24. -/
theorem nativeRealization_of_matrix_identities
    (hA : matrix 2420 2420 ambientA * embedding =
      embedding * Degrees12421792.Data1792.first)
    (hB : matrix 2420 2420 ambientB * embedding =
      embedding * Degrees12421792.Data1792.second) : Nonempty (Degrees12421792.NativeRealization
    Degrees12421792.Data1792.first Degrees12421792.Data1792.second) :=
  native1792_of_nonzero_quotient action2420 (Matrix.toLin' projection)
    projection_ne_zero (projection_first hA) (projection_second hB)
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Largest1792
