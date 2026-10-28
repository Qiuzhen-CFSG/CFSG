module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.Coordinates
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.Rank
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.SourceGeneratorA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.SourceGeneratorB
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.QuotientGeneratorA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.QuotientGeneratorB
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.NonzeroQuotient

/-!
# The native 1242-dimensional subquotient

The saved injective source map intertwines the genuine native 44 by dual-44
representation with the 1474-dimensional source matrices. This supplies an
honest action on the source. The saved nonzero quotient intertwines its two
generators with the transposed ATLAS matrices. Density gives surjectivity;
the quotient kernel is invariant under the full native group by generation.
Thus both source invariance and quotient invariance precede the realization.

Sources: James (1973), GM02 Proposition 5.1; Aschbacher–Smith K.4 p.457.
Saved witness provenance and ATLAS attribution: Subquotient1242/source/README.md.
-/

public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
open Degree220Pair.NativeActions.CertificatePacked TensorCoordinates

/-- Source invariance for the first native generator. -/
theorem embedding_first :
    (action1936 Degree220Pair.generatorA).comp (Matrix.toLin' embedding) =
      (Matrix.toLin' embedding).comp (Matrix.toLin' sourceA) := by
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  have hn := congrArg Matrix.transpose native_matrix_A
  rw [Matrix.transpose_transpose] at hn
  rw [hn]
  have hc := congrArg Matrix.transpose sourceGeneratorA
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at hc
  exact hc

/-- Source invariance for the second native generator. -/
theorem embedding_second :
    (action1936 Degree220Pair.generatorB).comp (Matrix.toLin' embedding) =
      (Matrix.toLin' embedding).comp (Matrix.toLin' sourceB) := by
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  have hn := congrArg Matrix.transpose native_matrix_B
  rw [Matrix.transpose_transpose] at hn
  rw [hn]
  have hc := congrArg Matrix.transpose sourceGeneratorB
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at hc
  exact hc

/-- The quotient retains the literal transpose convention at the first generator. -/
theorem quotient_first : quotientMap * sourceA =
    Degrees12421792.Data1242.first.transpose * quotientMap := by
  have h := quotientGeneratorA
  rw [target_matrix_A] at h
  have hc := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at hc
  exact hc

/-- The quotient retains the literal transpose convention at the second generator. -/
theorem quotient_second : quotientMap * sourceB =
    Degrees12421792.Data1242.second.transpose * quotientMap := by
  have h := quotientGeneratorB
  rw [target_matrix_B] at h
  have hc := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at hc
  exact hc

/-- Unconditional realization on the actual Witt-design M24 carrier. -/
theorem nativeRealization : Nonempty (Degrees12421792.NativeRealization
    Degrees12421792.Data1242.first Degrees12421792.Data1242.second) :=
  native1242_of_nonzero_subquotient action1936 sourceA sourceB
    (Matrix.toLin' embedding) embedding_injective embedding_first embedding_second
    quotientMap quotientMap_ne_zero quotient_first quotient_second
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
