module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Geometry
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.MatrixCertificates

/-!
# The native degree-252 sextet representation

The geometric comparison identifies the 1771 saved partitions with the native
sextets, retaining their point labels and the forward action of both standard
generators. The checked left inverse makes the saved covector map injective,
and the full row certificates intertwine the two literal candidate matrices.
Native generation then makes its image invariant under all of M24. Restricting
the sextet permutation representation to this image and transporting through
the injection gives the unconditional realization below.

This module discharges every premise of `native252OfCertificates`. Its separate
binary-model application retains matrix density for the parent degree-120/252
assembly. Both finite-certificate modules import the conditional assembly, so
the unconditional result is a further extension rather than a reverse import.

Sources: James, J. Algebra 27 (1973), 57–111; the larger binary models used in
GM02, Proposition 5.1. The literal data and conventions are documented in
`Degrees120252/source/README.md` and `Native252/source/README.md`.
-/

public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252

/-- The lawful action on 252 coordinates obtained from the native sextet space,
with the two literal candidate generator matrices. -/
def native252 : NativeRealization 252 matrix252 :=
  native252OfCertificates
    Native252.Geometry.pointParts_injective Native252.Geometry.pointParts_forward
    Native252.MatrixCertificates.embedding_injective
    Native252.MatrixCertificates.embedding_intertwines

/-- Unconditional native realization, with no irreducibility or density premise. -/
theorem nonempty_native252 : Nonempty (NativeRealization 252 matrix252) :=
  ⟨native252⟩

/-- The native comparison premise is discharged. The parent assembly supplies
the independent matrix-density certificate for absolute irreducibility. -/
def binaryModel252OfDensity
    (hA : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin 252) (Fin 252) (ZMod 2)),
      (∀ j, matrix252 j ∈ Q) → Q = ⊤) : BinaryModel 252 :=
  native252.binaryModel hA

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252
