module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.Data
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.Conditional
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.ExpansionChecks

/-!
# Left part of the exact degree-1792 singular expression

The two expanded generator tables and all four products have complete checked
certificates. Applying them to the structural assembly proves the exact first
plus fourth summands, using the original untransposed ATLAS matrices and fixed
packed left rows. This discharges the left-part premise of
`packedSingular_eq_singular_of_parts`; the singular-expression task retains
the assembly of both parts. See `LeftExpression/source/README.md` for the
factorization and source attribution.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix

/-- The fixed packed left rows equal the first plus fourth singular-expression
summands on the original untransposed generators, without additional premises. -/
theorem packedLeft_eq_leftExpression : packedLeft = leftExpression :=
  packedLeft_eq_leftExpression_of_checks
    RightCertificate.first_expanded_checked RightCertificate.second_expanded_checked
    LeftCertificate.tb_checked LeftCertificate.da_checked
    LeftCertificate.dab_checked LeftCertificate.left_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
