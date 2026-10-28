module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.ExpansionChecks
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Conditional

/-!
# Application of both complete expansion certificates

The exact right singular-expression assembly now requires only its five
independent product checks. Both original untransposed ATLAS generator tables
are expanded by the unconditional certificates, with every row and digit checked.
See `source/README.md` for source attribution and the remaining product contracts.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
open RightCertificate

/-- Discharge precisely the two expansion premises of the published assembly. -/
theorem packedRight_eq_rightExpression_of_product_checks
    (hba : Wide.checkRows 1792 Data1792.secondRows.toList wideFirst baRows = true)
    (htb : Wide.checkRows 1792 tRows wideSecond tbRows = true)
    (hub : Wide.checkRows 1792 uRows wideSecond ubRows = true)
    (hha : Wide.checkRows 1792 hRows wideFirst haRows = true)
    (hr : Wide.checkRows 1792 haRows wideSecond rightRows.toList = true) :
    packedRight = rightExpression :=
  packedRight_eq_rightExpression_of_checks first_expanded_checked second_expanded_checked
    hba htb hub hha hr

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
