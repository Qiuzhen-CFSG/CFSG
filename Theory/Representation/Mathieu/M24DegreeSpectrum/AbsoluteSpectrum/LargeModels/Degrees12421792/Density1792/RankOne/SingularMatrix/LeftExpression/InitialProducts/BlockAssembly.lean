module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks24

/-!
# Use the checked dense block in the fourth row quarter

The check on [1536,1600) discharges one of the seven blocks in [1344,1792).
The other six bounded checks remain explicit. These two applications feed
the fourth-quarter producer, then the full-list and exact matrix consumers.
See source/README.md.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts

theorem tb_quarter3_of_blocks
    (h21 : Wide.checkRows 1792 ((tRows.drop 1344).take 64)
      RightCertificate.wideSecond ((tbRows.drop 1344).take 64) = true)
    (h22 : Wide.checkRows 1792 ((tRows.drop 1408).take 64)
      RightCertificate.wideSecond ((tbRows.drop 1408).take 64) = true)
    (h23 : Wide.checkRows 1792 ((tRows.drop 1472).take 64)
      RightCertificate.wideSecond ((tbRows.drop 1472).take 64) = true)
    (h25 : Wide.checkRows 1792 ((tRows.drop 1600).take 64)
      RightCertificate.wideSecond ((tbRows.drop 1600).take 64) = true)
    (h26 : Wide.checkRows 1792 ((tRows.drop 1664).take 64)
      RightCertificate.wideSecond ((tbRows.drop 1664).take 64) = true)
    (h27 : Wide.checkRows 1792 ((tRows.drop 1728).take 64)
      RightCertificate.wideSecond ((tbRows.drop 1728).take 64) = true)
    : Wide.checkRows 1792 ((tRows.drop 1344).take 448)
      RightCertificate.wideSecond ((tbRows.drop 1344).take 448) = true := by
  apply product_range tRows RightCertificate.wideSecond tbRows
    1344 64 384 h21
  apply product_range tRows RightCertificate.wideSecond tbRows
    1408 64 320 h22
  apply product_range tRows RightCertificate.wideSecond tbRows
    1472 64 256 h23
  apply product_range tRows RightCertificate.wideSecond tbRows
    1536 64 192 Block24.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows
    1600 64 128 h25
  apply product_range tRows RightCertificate.wideSecond tbRows
    1664 64 64 h26
  exact h27

theorem da_quarter3_of_blocks
    (h21 : Wide.checkRows 1792 ((dRows.drop 1344).take 64)
      RightCertificate.wideFirst ((daRows.drop 1344).take 64) = true)
    (h22 : Wide.checkRows 1792 ((dRows.drop 1408).take 64)
      RightCertificate.wideFirst ((daRows.drop 1408).take 64) = true)
    (h23 : Wide.checkRows 1792 ((dRows.drop 1472).take 64)
      RightCertificate.wideFirst ((daRows.drop 1472).take 64) = true)
    (h25 : Wide.checkRows 1792 ((dRows.drop 1600).take 64)
      RightCertificate.wideFirst ((daRows.drop 1600).take 64) = true)
    (h26 : Wide.checkRows 1792 ((dRows.drop 1664).take 64)
      RightCertificate.wideFirst ((daRows.drop 1664).take 64) = true)
    (h27 : Wide.checkRows 1792 ((dRows.drop 1728).take 64)
      RightCertificate.wideFirst ((daRows.drop 1728).take 64) = true)
    : Wide.checkRows 1792 ((dRows.drop 1344).take 448)
      RightCertificate.wideFirst ((daRows.drop 1344).take 448) = true := by
  apply product_range dRows RightCertificate.wideFirst daRows
    1344 64 384 h21
  apply product_range dRows RightCertificate.wideFirst daRows
    1408 64 320 h22
  apply product_range dRows RightCertificate.wideFirst daRows
    1472 64 256 h23
  apply product_range dRows RightCertificate.wideFirst daRows
    1536 64 192 Block24.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows
    1600 64 128 h25
  apply product_range dRows RightCertificate.wideFirst daRows
    1664 64 64 h26
  exact h27

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts

