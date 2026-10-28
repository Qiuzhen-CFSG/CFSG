module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [606208, 614400).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B021
private theorem c606208 : checkChunk 606208 128 = true := by decide +kernel
private theorem c606336 : checkChunk 606336 128 = true := by decide +kernel
private theorem c606464 : checkChunk 606464 128 = true := by decide +kernel
private theorem c606592 : checkChunk 606592 128 = true := by decide +kernel
private theorem c606720 : checkChunk 606720 128 = true := by decide +kernel
private theorem c606848 : checkChunk 606848 128 = true := by decide +kernel
private theorem c606976 : checkChunk 606976 128 = true := by decide +kernel
private theorem c607104 : checkChunk 607104 128 = true := by decide +kernel
private theorem c607232 : checkChunk 607232 128 = true := by decide +kernel
private theorem c607360 : checkChunk 607360 128 = true := by decide +kernel
private theorem c607488 : checkChunk 607488 128 = true := by decide +kernel
private theorem c607616 : checkChunk 607616 128 = true := by decide +kernel
private theorem c607744 : checkChunk 607744 128 = true := by decide +kernel
private theorem c607872 : checkChunk 607872 128 = true := by decide +kernel
private theorem c608000 : checkChunk 608000 128 = true := by decide +kernel
private theorem c608128 : checkChunk 608128 128 = true := by decide +kernel
private theorem c608256 : checkChunk 608256 128 = true := by decide +kernel
private theorem c608384 : checkChunk 608384 128 = true := by decide +kernel
private theorem c608512 : checkChunk 608512 128 = true := by decide +kernel
private theorem c608640 : checkChunk 608640 128 = true := by decide +kernel
private theorem c608768 : checkChunk 608768 128 = true := by decide +kernel
private theorem c608896 : checkChunk 608896 128 = true := by decide +kernel
private theorem c609024 : checkChunk 609024 128 = true := by decide +kernel
private theorem c609152 : checkChunk 609152 128 = true := by decide +kernel
private theorem c609280 : checkChunk 609280 128 = true := by decide +kernel
private theorem c609408 : checkChunk 609408 128 = true := by decide +kernel
private theorem c609536 : checkChunk 609536 128 = true := by decide +kernel
private theorem c609664 : checkChunk 609664 128 = true := by decide +kernel
private theorem c609792 : checkChunk 609792 128 = true := by decide +kernel
private theorem c609920 : checkChunk 609920 128 = true := by decide +kernel
private theorem c610048 : checkChunk 610048 128 = true := by decide +kernel
private theorem c610176 : checkChunk 610176 128 = true := by decide +kernel
private theorem c610304 : checkChunk 610304 128 = true := by decide +kernel
private theorem c610432 : checkChunk 610432 128 = true := by decide +kernel
private theorem c610560 : checkChunk 610560 128 = true := by decide +kernel
private theorem c610688 : checkChunk 610688 128 = true := by decide +kernel
private theorem c610816 : checkChunk 610816 128 = true := by decide +kernel
private theorem c610944 : checkChunk 610944 128 = true := by decide +kernel
private theorem c611072 : checkChunk 611072 128 = true := by decide +kernel
private theorem c611200 : checkChunk 611200 128 = true := by decide +kernel
private theorem c611328 : checkChunk 611328 128 = true := by decide +kernel
private theorem c611456 : checkChunk 611456 128 = true := by decide +kernel
private theorem c611584 : checkChunk 611584 128 = true := by decide +kernel
private theorem c611712 : checkChunk 611712 128 = true := by decide +kernel
private theorem c611840 : checkChunk 611840 128 = true := by decide +kernel
private theorem c611968 : checkChunk 611968 128 = true := by decide +kernel
private theorem c612096 : checkChunk 612096 128 = true := by decide +kernel
private theorem c612224 : checkChunk 612224 128 = true := by decide +kernel
private theorem c612352 : checkChunk 612352 128 = true := by decide +kernel
private theorem c612480 : checkChunk 612480 128 = true := by decide +kernel
private theorem c612608 : checkChunk 612608 128 = true := by decide +kernel
private theorem c612736 : checkChunk 612736 128 = true := by decide +kernel
private theorem c612864 : checkChunk 612864 128 = true := by decide +kernel
private theorem c612992 : checkChunk 612992 128 = true := by decide +kernel
private theorem c613120 : checkChunk 613120 128 = true := by decide +kernel
private theorem c613248 : checkChunk 613248 128 = true := by decide +kernel
private theorem c613376 : checkChunk 613376 128 = true := by decide +kernel
private theorem c613504 : checkChunk 613504 128 = true := by decide +kernel
private theorem c613632 : checkChunk 613632 128 = true := by decide +kernel
private theorem c613760 : checkChunk 613760 128 = true := by decide +kernel
private theorem c613888 : checkChunk 613888 128 = true := by decide +kernel
private theorem c614016 : checkChunk 614016 128 = true := by decide +kernel
private theorem c614144 : checkChunk 614144 128 = true := by decide +kernel
private theorem c614272 : checkChunk 614272 128 = true := by decide +kernel

public theorem checked : Checked 606208 614400 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 606208 128 c606208) (checkChunk_sound 606336 128 c606336)) (Checked.append (checkChunk_sound 606464 128 c606464) (checkChunk_sound 606592 128 c606592))) (Checked.append (Checked.append (checkChunk_sound 606720 128 c606720) (checkChunk_sound 606848 128 c606848)) (Checked.append (checkChunk_sound 606976 128 c606976) (checkChunk_sound 607104 128 c607104)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 607232 128 c607232) (checkChunk_sound 607360 128 c607360)) (Checked.append (checkChunk_sound 607488 128 c607488) (checkChunk_sound 607616 128 c607616))) (Checked.append (Checked.append (checkChunk_sound 607744 128 c607744) (checkChunk_sound 607872 128 c607872)) (Checked.append (checkChunk_sound 608000 128 c608000) (checkChunk_sound 608128 128 c608128))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 608256 128 c608256) (checkChunk_sound 608384 128 c608384)) (Checked.append (checkChunk_sound 608512 128 c608512) (checkChunk_sound 608640 128 c608640))) (Checked.append (Checked.append (checkChunk_sound 608768 128 c608768) (checkChunk_sound 608896 128 c608896)) (Checked.append (checkChunk_sound 609024 128 c609024) (checkChunk_sound 609152 128 c609152)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 609280 128 c609280) (checkChunk_sound 609408 128 c609408)) (Checked.append (checkChunk_sound 609536 128 c609536) (checkChunk_sound 609664 128 c609664))) (Checked.append (Checked.append (checkChunk_sound 609792 128 c609792) (checkChunk_sound 609920 128 c609920)) (Checked.append (checkChunk_sound 610048 128 c610048) (checkChunk_sound 610176 128 c610176)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 610304 128 c610304) (checkChunk_sound 610432 128 c610432)) (Checked.append (checkChunk_sound 610560 128 c610560) (checkChunk_sound 610688 128 c610688))) (Checked.append (Checked.append (checkChunk_sound 610816 128 c610816) (checkChunk_sound 610944 128 c610944)) (Checked.append (checkChunk_sound 611072 128 c611072) (checkChunk_sound 611200 128 c611200)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 611328 128 c611328) (checkChunk_sound 611456 128 c611456)) (Checked.append (checkChunk_sound 611584 128 c611584) (checkChunk_sound 611712 128 c611712))) (Checked.append (Checked.append (checkChunk_sound 611840 128 c611840) (checkChunk_sound 611968 128 c611968)) (Checked.append (checkChunk_sound 612096 128 c612096) (checkChunk_sound 612224 128 c612224))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 612352 128 c612352) (checkChunk_sound 612480 128 c612480)) (Checked.append (checkChunk_sound 612608 128 c612608) (checkChunk_sound 612736 128 c612736))) (Checked.append (Checked.append (checkChunk_sound 612864 128 c612864) (checkChunk_sound 612992 128 c612992)) (Checked.append (checkChunk_sound 613120 128 c613120) (checkChunk_sound 613248 128 c613248)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 613376 128 c613376) (checkChunk_sound 613504 128 c613504)) (Checked.append (checkChunk_sound 613632 128 c613632) (checkChunk_sound 613760 128 c613760))) (Checked.append (Checked.append (checkChunk_sound 613888 128 c613888) (checkChunk_sound 614016 128 c614016)) (Checked.append (checkChunk_sound 614144 128 c614144) (checkChunk_sound 614272 128 c614272)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B021
