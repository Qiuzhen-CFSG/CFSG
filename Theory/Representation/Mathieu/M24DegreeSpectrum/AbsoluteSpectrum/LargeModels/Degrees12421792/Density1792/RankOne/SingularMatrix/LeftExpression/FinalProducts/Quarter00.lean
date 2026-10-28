module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks03
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks04
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks05
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks06

/-!
# Final left products on rows 0–447

Seven kernel-checked blocks certify all 1792 columns of both final products
on the first 448 rows. Append composition and the take/drop identities join
the exact published source masks; no expanded-table or earlier-product premise
is required. These exports discharge the first-quarter arguments of
`LeftCertificate.dab_checked_of_quarters` and `left_checked_of_quarters`.
See `source/README.md` for the original ATLAS matrices, the factorization,
and the witness/checking separation.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.FinalProducts.Quarter00

private theorem take_step (a w c : List Nat) (i k n : Nat)
    (h₁ : Wide.checkRows 1792 ((a.drop i).take k) w ((c.drop i).take k) = true)
    (h₂ : Wide.checkRows 1792 ((a.drop (i+k)).take n) w
      ((c.drop (i+k)).take n) = true) :
    Wide.checkRows 1792 ((a.drop i).take (k+n)) w
      ((c.drop i).take (k+n)) = true := by
  have h := Wide.checkRows_append 1792 ((a.drop i).take k)
    ((a.drop (i+k)).take n) w ((c.drop i).take k)
    ((c.drop (i+k)).take n) h₁ h₂
  simpa only [List.take_add, List.drop_drop, Nat.add_comm] using h

/-- Complete dab product check for the first 448 source rows. -/
theorem dab_checked :
    Wide.checkRows 1792 ((daRows.drop 0).take 448) RightCertificate.wideSecond
      ((dabRows.drop 0).take 448) = true := by
  apply take_step daRows RightCertificate.wideSecond dabRows 0 64 384
    Block00.dab_checked
  apply take_step daRows RightCertificate.wideSecond dabRows 64 64 320
    Block01.dab_checked
  apply take_step daRows RightCertificate.wideSecond dabRows 128 64 256
    Block02.dab_checked
  apply take_step daRows RightCertificate.wideSecond dabRows 192 64 192
    Block03.dab_checked
  apply take_step daRows RightCertificate.wideSecond dabRows 256 64 128
    Block04.dab_checked
  exact take_step daRows RightCertificate.wideSecond dabRows 320 64 64
    Block05.dab_checked Block06.dab_checked

/-- Complete left product check for the first 448 source rows. -/
theorem left_checked :
    Wide.checkRows 1792 ((eRows.drop 0).take 448) RightCertificate.wideSecond
      ((leftRows.toList.drop 0).take 448) = true := by
  apply take_step eRows RightCertificate.wideSecond leftRows.toList 0 64 384
    Block00.left_checked
  apply take_step eRows RightCertificate.wideSecond leftRows.toList 64 64 320
    Block01.left_checked
  apply take_step eRows RightCertificate.wideSecond leftRows.toList 128 64 256
    Block02.left_checked
  apply take_step eRows RightCertificate.wideSecond leftRows.toList 192 64 192
    Block03.left_checked
  apply take_step eRows RightCertificate.wideSecond leftRows.toList 256 64 128
    Block04.left_checked
  exact take_step eRows RightCertificate.wideSecond leftRows.toList 320 64 64
    Block05.left_checked Block06.left_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.FinalProducts.Quarter00
