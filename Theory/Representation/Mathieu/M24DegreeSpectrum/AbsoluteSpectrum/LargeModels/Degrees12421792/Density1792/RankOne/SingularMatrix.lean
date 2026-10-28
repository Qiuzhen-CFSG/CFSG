module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.Recombine

/-!
# Assembly of the exact packed singular expression

The two certified parts have a checked sum equal to the unchanged published
packed matrix. Their full matrix-product identities and the additive splitting
of the four summands prove `packedSingular_eq_singular` without additional
hypotheses. This discharges the row-equality premise of
`rankOne_mem_of_packed_certificates`.

The statements use the original untransposed ATLAS matrices and the original
four summands of `CertificateData.singular`. See `SingularMatrix/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate
open SingularMatrix

/-- Conditional assembly only: both literal matrix-product identities must be proved. -/
theorem packedSingular_eq_singular_of_parts
    (hleft : packedLeft = leftExpression) (hright : packedRight = rightExpression) :
    packedSingular = singular := by
  rw [← packedLeft_add_packedRight, hleft, hright, expression_split]

/-- Transport the exact completion along the two product certificates. -/
theorem packedCompletion_eq_of_parts
    (hleft : packedLeft = leftExpression) (hright : packedRight = rightExpression) :
    packedCompletion = singular + rankOne := by
  rw [packedCompletion, packedSingular_eq_singular_of_parts hleft hright]

/-- The published packed rows decode to the exact four-summand expression on
the original untransposed ATLAS generators. All product and row checks are
discharged by the two part certificates and their checked recombination. -/
theorem packedSingular_eq_singular : packedSingular = singular :=
  packedSingular_eq_singular_of_parts
    packedLeft_eq_leftExpression packedRight_eq_rightExpression

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate
