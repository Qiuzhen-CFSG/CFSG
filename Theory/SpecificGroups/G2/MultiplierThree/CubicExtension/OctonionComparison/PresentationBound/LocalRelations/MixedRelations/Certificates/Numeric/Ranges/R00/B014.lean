module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [122880, 131072).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B014
private theorem c122880 : checkChunk 122880 128 = true := by decide +kernel
private theorem c123008 : checkChunk 123008 128 = true := by decide +kernel
private theorem c123136 : checkChunk 123136 128 = true := by decide +kernel
private theorem c123264 : checkChunk 123264 128 = true := by decide +kernel
private theorem c123392 : checkChunk 123392 128 = true := by decide +kernel
private theorem c123520 : checkChunk 123520 128 = true := by decide +kernel
private theorem c123648 : checkChunk 123648 128 = true := by decide +kernel
private theorem c123776 : checkChunk 123776 128 = true := by decide +kernel
private theorem c123904 : checkChunk 123904 128 = true := by decide +kernel
private theorem c124032 : checkChunk 124032 128 = true := by decide +kernel
private theorem c124160 : checkChunk 124160 128 = true := by decide +kernel
private theorem c124288 : checkChunk 124288 128 = true := by decide +kernel
private theorem c124416 : checkChunk 124416 128 = true := by decide +kernel
private theorem c124544 : checkChunk 124544 128 = true := by decide +kernel
private theorem c124672 : checkChunk 124672 128 = true := by decide +kernel
private theorem c124800 : checkChunk 124800 128 = true := by decide +kernel
private theorem c124928 : checkChunk 124928 128 = true := by decide +kernel
private theorem c125056 : checkChunk 125056 128 = true := by decide +kernel
private theorem c125184 : checkChunk 125184 128 = true := by decide +kernel
private theorem c125312 : checkChunk 125312 128 = true := by decide +kernel
private theorem c125440 : checkChunk 125440 128 = true := by decide +kernel
private theorem c125568 : checkChunk 125568 128 = true := by decide +kernel
private theorem c125696 : checkChunk 125696 128 = true := by decide +kernel
private theorem c125824 : checkChunk 125824 128 = true := by decide +kernel
private theorem c125952 : checkChunk 125952 128 = true := by decide +kernel
private theorem c126080 : checkChunk 126080 128 = true := by decide +kernel
private theorem c126208 : checkChunk 126208 128 = true := by decide +kernel
private theorem c126336 : checkChunk 126336 128 = true := by decide +kernel
private theorem c126464 : checkChunk 126464 128 = true := by decide +kernel
private theorem c126592 : checkChunk 126592 128 = true := by decide +kernel
private theorem c126720 : checkChunk 126720 128 = true := by decide +kernel
private theorem c126848 : checkChunk 126848 128 = true := by decide +kernel
private theorem c126976 : checkChunk 126976 128 = true := by decide +kernel
private theorem c127104 : checkChunk 127104 128 = true := by decide +kernel
private theorem c127232 : checkChunk 127232 128 = true := by decide +kernel
private theorem c127360 : checkChunk 127360 128 = true := by decide +kernel
private theorem c127488 : checkChunk 127488 128 = true := by decide +kernel
private theorem c127616 : checkChunk 127616 128 = true := by decide +kernel
private theorem c127744 : checkChunk 127744 128 = true := by decide +kernel
private theorem c127872 : checkChunk 127872 128 = true := by decide +kernel
private theorem c128000 : checkChunk 128000 128 = true := by decide +kernel
private theorem c128128 : checkChunk 128128 128 = true := by decide +kernel
private theorem c128256 : checkChunk 128256 128 = true := by decide +kernel
private theorem c128384 : checkChunk 128384 128 = true := by decide +kernel
private theorem c128512 : checkChunk 128512 128 = true := by decide +kernel
private theorem c128640 : checkChunk 128640 128 = true := by decide +kernel
private theorem c128768 : checkChunk 128768 128 = true := by decide +kernel
private theorem c128896 : checkChunk 128896 128 = true := by decide +kernel
private theorem c129024 : checkChunk 129024 128 = true := by decide +kernel
private theorem c129152 : checkChunk 129152 128 = true := by decide +kernel
private theorem c129280 : checkChunk 129280 128 = true := by decide +kernel
private theorem c129408 : checkChunk 129408 128 = true := by decide +kernel
private theorem c129536 : checkChunk 129536 128 = true := by decide +kernel
private theorem c129664 : checkChunk 129664 128 = true := by decide +kernel
private theorem c129792 : checkChunk 129792 128 = true := by decide +kernel
private theorem c129920 : checkChunk 129920 128 = true := by decide +kernel
private theorem c130048 : checkChunk 130048 128 = true := by decide +kernel
private theorem c130176 : checkChunk 130176 128 = true := by decide +kernel
private theorem c130304 : checkChunk 130304 128 = true := by decide +kernel
private theorem c130432 : checkChunk 130432 128 = true := by decide +kernel
private theorem c130560 : checkChunk 130560 128 = true := by decide +kernel
private theorem c130688 : checkChunk 130688 128 = true := by decide +kernel
private theorem c130816 : checkChunk 130816 128 = true := by decide +kernel
private theorem c130944 : checkChunk 130944 128 = true := by decide +kernel

public theorem checked : Checked 122880 131072 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 122880 128 c122880) (checkChunk_sound 123008 128 c123008)) (Checked.append (checkChunk_sound 123136 128 c123136) (checkChunk_sound 123264 128 c123264))) (Checked.append (Checked.append (checkChunk_sound 123392 128 c123392) (checkChunk_sound 123520 128 c123520)) (Checked.append (checkChunk_sound 123648 128 c123648) (checkChunk_sound 123776 128 c123776)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 123904 128 c123904) (checkChunk_sound 124032 128 c124032)) (Checked.append (checkChunk_sound 124160 128 c124160) (checkChunk_sound 124288 128 c124288))) (Checked.append (Checked.append (checkChunk_sound 124416 128 c124416) (checkChunk_sound 124544 128 c124544)) (Checked.append (checkChunk_sound 124672 128 c124672) (checkChunk_sound 124800 128 c124800))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 124928 128 c124928) (checkChunk_sound 125056 128 c125056)) (Checked.append (checkChunk_sound 125184 128 c125184) (checkChunk_sound 125312 128 c125312))) (Checked.append (Checked.append (checkChunk_sound 125440 128 c125440) (checkChunk_sound 125568 128 c125568)) (Checked.append (checkChunk_sound 125696 128 c125696) (checkChunk_sound 125824 128 c125824)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 125952 128 c125952) (checkChunk_sound 126080 128 c126080)) (Checked.append (checkChunk_sound 126208 128 c126208) (checkChunk_sound 126336 128 c126336))) (Checked.append (Checked.append (checkChunk_sound 126464 128 c126464) (checkChunk_sound 126592 128 c126592)) (Checked.append (checkChunk_sound 126720 128 c126720) (checkChunk_sound 126848 128 c126848)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 126976 128 c126976) (checkChunk_sound 127104 128 c127104)) (Checked.append (checkChunk_sound 127232 128 c127232) (checkChunk_sound 127360 128 c127360))) (Checked.append (Checked.append (checkChunk_sound 127488 128 c127488) (checkChunk_sound 127616 128 c127616)) (Checked.append (checkChunk_sound 127744 128 c127744) (checkChunk_sound 127872 128 c127872)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 128000 128 c128000) (checkChunk_sound 128128 128 c128128)) (Checked.append (checkChunk_sound 128256 128 c128256) (checkChunk_sound 128384 128 c128384))) (Checked.append (Checked.append (checkChunk_sound 128512 128 c128512) (checkChunk_sound 128640 128 c128640)) (Checked.append (checkChunk_sound 128768 128 c128768) (checkChunk_sound 128896 128 c128896))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 129024 128 c129024) (checkChunk_sound 129152 128 c129152)) (Checked.append (checkChunk_sound 129280 128 c129280) (checkChunk_sound 129408 128 c129408))) (Checked.append (Checked.append (checkChunk_sound 129536 128 c129536) (checkChunk_sound 129664 128 c129664)) (Checked.append (checkChunk_sound 129792 128 c129792) (checkChunk_sound 129920 128 c129920)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 130048 128 c130048) (checkChunk_sound 130176 128 c130176)) (Checked.append (checkChunk_sound 130304 128 c130304) (checkChunk_sound 130432 128 c130432))) (Checked.append (Checked.append (checkChunk_sound 130560 128 c130560) (checkChunk_sound 130688 128 c130688)) (Checked.append (checkChunk_sound 130816 128 c130816) (checkChunk_sound 130944 128 c130944)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B014
