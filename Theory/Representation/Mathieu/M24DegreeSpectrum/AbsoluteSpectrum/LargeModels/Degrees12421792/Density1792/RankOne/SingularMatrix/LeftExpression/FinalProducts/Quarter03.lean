module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks21
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks22
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks23
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks24
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks25
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks26
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks27

/-!
# Final left products on rows 1344–1791

Seven consecutive 64-row checks certify both DAB = (DA)B and L = EB on the
fourth quarter of the fixed tables. Each block checks all 1792 columns and
identifies its masks with the published inputs and outputs. Block 23 is reused
unchanged. The checks compose by splitting list prefixes; no matrix-product,
expansion, rank, or group hypothesis is used.

These exports discharge the fourth-quarter premises of
`LeftCertificate.dab_checked_of_quarters` and
`LeftCertificate.left_checked_of_quarters`. See `source/README.md` for the
original ATLAS generators, the factorization, and source attribution.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.FinalProducts.Quarter03

private theorem checkRows_take_add (a w c : List Nat) (i k l : Nat)
    (h₁ : Wide.checkRows 1792 ((a.drop i).take k) w ((c.drop i).take k) = true)
    (h₂ : Wide.checkRows 1792 ((a.drop (i + k)).take l) w
      ((c.drop (i + k)).take l) = true) :
    Wide.checkRows 1792 ((a.drop i).take (k + l)) w
      ((c.drop i).take (k + l)) = true := by
  rw [List.take_add, List.take_add]
  apply Wide.checkRows_append _ _ _ _ _ _ h₁
  simpa only [List.drop_drop, Nat.add_comm] using h₂

/-- The complete fourth-quarter check for DAB = (DA)B. -/
theorem dab_checked :
    Wide.checkRows 1792 ((daRows.drop 1344).take 448) RightCertificate.wideSecond
      ((dabRows.drop 1344).take 448) = true := by
  apply checkRows_take_add _ _ _ 1344 64 384 Block21.dab_checked
  apply checkRows_take_add _ _ _ 1408 64 320 Block22.dab_checked
  apply checkRows_take_add _ _ _ 1472 64 256 Block23.dab_checked
  apply checkRows_take_add _ _ _ 1536 64 192 Block24.dab_checked
  apply checkRows_take_add _ _ _ 1600 64 128 Block25.dab_checked
  apply checkRows_take_add _ _ _ 1664 64 64 Block26.dab_checked
  exact Block27.dab_checked

/-- The complete fourth-quarter check for the fixed final rows L = EB. -/
theorem left_checked :
    Wide.checkRows 1792 ((eRows.drop 1344).take 448) RightCertificate.wideSecond
      ((leftRows.toList.drop 1344).take 448) = true := by
  apply checkRows_take_add _ _ _ 1344 64 384 Block21.left_checked
  apply checkRows_take_add _ _ _ 1408 64 320 Block22.left_checked
  apply checkRows_take_add _ _ _ 1472 64 256 Block23.left_checked
  apply checkRows_take_add _ _ _ 1536 64 192 Block24.left_checked
  apply checkRows_take_add _ _ _ 1600 64 128 Block25.left_checked
  apply checkRows_take_add _ _ _ 1664 64 64 Block26.left_checked
  exact Block27.left_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.FinalProducts.Quarter03
