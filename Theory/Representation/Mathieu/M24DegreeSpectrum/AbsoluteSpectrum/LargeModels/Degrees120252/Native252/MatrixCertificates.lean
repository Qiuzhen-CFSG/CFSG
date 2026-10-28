module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.MatrixCertificates.Selection
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.MatrixCertificates.Rows
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252

/-!
# Certified linear premises of the native degree-252 realization

The selected left inverse proves injectivity of the rectangular map, and the
packed row checks prove equivariance under both native generators. Applying
`native252OfCertificates` leaves only the independent native geometry explicit.

The data describe the 1771-by-252 embedding in the native sextet permutation
space. The checks retain the literal ordering and the forward-index convention.
All numerical equalities are reduced by the Lean kernel. Sources: James,
J. Algebra 27 (1973), 57–111; GM02, Proposition 5.1; the saved ATLAS candidates
and sextet construction documented in `../source/README.md`.
-/

set_option Elab.async false
public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.MatrixCertificates
open scoped Pointwise

/-- Both literal generators intertwine the full rectangular embedding. -/
theorem embedding_intertwines : ∀ j i k,
    (embeddingMatrix * matrix252 j) (forward j i) k = embeddingMatrix i k :=
  intertwining_of_rows rows252_length packed_rows

/-- Only the independent native geometry remains in the realization consumer. -/
noncomputable def native252OfGeometry
    (hp : Function.Injective pointParts)
    (hm : ∀ j i, actor j • pointParts i = pointParts (forward j i)) :
    NativeRealization 252 matrix252 :=
  native252OfCertificates hp hm embedding_injective embedding_intertwines

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.MatrixCertificates
