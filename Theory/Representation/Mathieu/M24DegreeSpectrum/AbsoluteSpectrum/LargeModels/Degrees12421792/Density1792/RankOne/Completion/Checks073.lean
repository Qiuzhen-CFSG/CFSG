module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Completion.Data

/-!
# Completion elimination pivots 1168 through 1183

The kernel checks block 073 against the literal source rows, verifying its
source indices, XOR reductions and descending pivots. Earlier candidate rows
are fixed data; their validity is supplied by the final completion assembly.
Source and certificate conventions: `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.CompletionCertificate

set_option maxRecDepth 8192 in
theorem block073_checked : blockCheck 73 = true := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.CompletionCertificate
