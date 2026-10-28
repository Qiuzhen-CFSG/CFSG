module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Conditional
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.ExpansionChecks
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.InitialProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.FinalProducts

/-!
# Right part of the exact degree-1792 singular expression

The two expanded generator tables and all five products have complete checked
certificates. Applying them to the structural assembly proves the exact second
plus third summands, using the original untransposed ATLAS matrices and fixed
packed right rows. This discharges the right-part premise of
`packedSingular_eq_singular_of_parts`; the independent left part remains with
that theorem's assembly owner. See `RightExpression/source/README.md` for the
factorization and source attribution.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
open RightCertificate

/-- The fixed packed right rows equal the second plus third singular-expression
summands on the original untransposed generators, without additional premises. -/
theorem packedRight_eq_rightExpression : packedRight = rightExpression :=
  packedRight_eq_rightExpression_of_checks
    first_expanded_checked second_expanded_checked
    ba_checked tb_checked ub_checked ha_checked right_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
