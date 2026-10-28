module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Largest1792.Transport
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Largest1792.GeneratorA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Largest1792.GeneratorB

/-!
# The native 1792-dimensional quotient

The two saved generator identities now discharge the native quotient transport.
The genuine source is the native code tensor the 220b module. Density supplies
surjectivity from a nonzero entry of the saved quotient map. The target acts by
the transposes of the raw ATLAS matrices, as required by the public interface.

Sources: James (1973), GM02 Proposition 5.1; Aschbacher–Smith K.4 p.457.
Witness provenance and ATLAS attribution: Largest1792/source/README.md.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Largest1792

/-- Unconditional realization on the actual Witt-design M24 carrier. -/
theorem nativeRealization : Nonempty (Degrees12421792.NativeRealization
    Degrees12421792.Data1792.first Degrees12421792.Data1792.second) := by
  have hA := generatorA
  have hB := generatorB
  rw [target_matrix_A] at hA
  rw [target_matrix_B] at hB
  exact nativeRealization_of_matrix_identities hA hB
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Largest1792
