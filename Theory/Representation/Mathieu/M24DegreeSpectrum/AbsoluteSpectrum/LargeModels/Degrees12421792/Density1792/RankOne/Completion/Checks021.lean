module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Completion.Data

/-!
# Completion elimination pivots 336 through 351

This kernel check validates the original row indices, XOR reductions and
descending pivots in block 021 of the fixed degree-1792 completion.
The earlier candidate rows are fixed data; their mathematical validity is
supplied by the full assembly in `../Completion.lean`.
See `source/README.md` for the source, row conventions and reproduction.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.CompletionCertificate

set_option maxRecDepth 8192 in
theorem block021_checked : blockCheck 21 = true := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.CompletionCertificate

