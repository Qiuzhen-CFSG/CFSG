module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [286720, 294912).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B008
private theorem c286720 : checkChunk 286720 128 = true := by decide +kernel
private theorem c286848 : checkChunk 286848 128 = true := by decide +kernel
private theorem c286976 : checkChunk 286976 128 = true := by decide +kernel
private theorem c287104 : checkChunk 287104 128 = true := by decide +kernel
private theorem c287232 : checkChunk 287232 128 = true := by decide +kernel
private theorem c287360 : checkChunk 287360 128 = true := by decide +kernel
private theorem c287488 : checkChunk 287488 128 = true := by decide +kernel
private theorem c287616 : checkChunk 287616 128 = true := by decide +kernel
private theorem c287744 : checkChunk 287744 128 = true := by decide +kernel
private theorem c287872 : checkChunk 287872 128 = true := by decide +kernel
private theorem c288000 : checkChunk 288000 128 = true := by decide +kernel
private theorem c288128 : checkChunk 288128 128 = true := by decide +kernel
private theorem c288256 : checkChunk 288256 128 = true := by decide +kernel
private theorem c288384 : checkChunk 288384 128 = true := by decide +kernel
private theorem c288512 : checkChunk 288512 128 = true := by decide +kernel
private theorem c288640 : checkChunk 288640 128 = true := by decide +kernel
private theorem c288768 : checkChunk 288768 128 = true := by decide +kernel
private theorem c288896 : checkChunk 288896 128 = true := by decide +kernel
private theorem c289024 : checkChunk 289024 128 = true := by decide +kernel
private theorem c289152 : checkChunk 289152 128 = true := by decide +kernel
private theorem c289280 : checkChunk 289280 128 = true := by decide +kernel
private theorem c289408 : checkChunk 289408 128 = true := by decide +kernel
private theorem c289536 : checkChunk 289536 128 = true := by decide +kernel
private theorem c289664 : checkChunk 289664 128 = true := by decide +kernel
private theorem c289792 : checkChunk 289792 128 = true := by decide +kernel
private theorem c289920 : checkChunk 289920 128 = true := by decide +kernel
private theorem c290048 : checkChunk 290048 128 = true := by decide +kernel
private theorem c290176 : checkChunk 290176 128 = true := by decide +kernel
private theorem c290304 : checkChunk 290304 128 = true := by decide +kernel
private theorem c290432 : checkChunk 290432 128 = true := by decide +kernel
private theorem c290560 : checkChunk 290560 128 = true := by decide +kernel
private theorem c290688 : checkChunk 290688 128 = true := by decide +kernel
private theorem c290816 : checkChunk 290816 128 = true := by decide +kernel
private theorem c290944 : checkChunk 290944 128 = true := by decide +kernel
private theorem c291072 : checkChunk 291072 128 = true := by decide +kernel
private theorem c291200 : checkChunk 291200 128 = true := by decide +kernel
private theorem c291328 : checkChunk 291328 128 = true := by decide +kernel
private theorem c291456 : checkChunk 291456 128 = true := by decide +kernel
private theorem c291584 : checkChunk 291584 128 = true := by decide +kernel
private theorem c291712 : checkChunk 291712 128 = true := by decide +kernel
private theorem c291840 : checkChunk 291840 128 = true := by decide +kernel
private theorem c291968 : checkChunk 291968 128 = true := by decide +kernel
private theorem c292096 : checkChunk 292096 128 = true := by decide +kernel
private theorem c292224 : checkChunk 292224 128 = true := by decide +kernel
private theorem c292352 : checkChunk 292352 128 = true := by decide +kernel
private theorem c292480 : checkChunk 292480 128 = true := by decide +kernel
private theorem c292608 : checkChunk 292608 128 = true := by decide +kernel
private theorem c292736 : checkChunk 292736 128 = true := by decide +kernel
private theorem c292864 : checkChunk 292864 128 = true := by decide +kernel
private theorem c292992 : checkChunk 292992 128 = true := by decide +kernel
private theorem c293120 : checkChunk 293120 128 = true := by decide +kernel
private theorem c293248 : checkChunk 293248 128 = true := by decide +kernel
private theorem c293376 : checkChunk 293376 128 = true := by decide +kernel
private theorem c293504 : checkChunk 293504 128 = true := by decide +kernel
private theorem c293632 : checkChunk 293632 128 = true := by decide +kernel
private theorem c293760 : checkChunk 293760 128 = true := by decide +kernel
private theorem c293888 : checkChunk 293888 128 = true := by decide +kernel
private theorem c294016 : checkChunk 294016 128 = true := by decide +kernel
private theorem c294144 : checkChunk 294144 128 = true := by decide +kernel
private theorem c294272 : checkChunk 294272 128 = true := by decide +kernel
private theorem c294400 : checkChunk 294400 128 = true := by decide +kernel
private theorem c294528 : checkChunk 294528 128 = true := by decide +kernel
private theorem c294656 : checkChunk 294656 128 = true := by decide +kernel
private theorem c294784 : checkChunk 294784 128 = true := by decide +kernel

public theorem checked : Checked 286720 294912 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 286720 128 c286720) (checkChunk_sound 286848 128 c286848)) (Checked.append (checkChunk_sound 286976 128 c286976) (checkChunk_sound 287104 128 c287104))) (Checked.append (Checked.append (checkChunk_sound 287232 128 c287232) (checkChunk_sound 287360 128 c287360)) (Checked.append (checkChunk_sound 287488 128 c287488) (checkChunk_sound 287616 128 c287616)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 287744 128 c287744) (checkChunk_sound 287872 128 c287872)) (Checked.append (checkChunk_sound 288000 128 c288000) (checkChunk_sound 288128 128 c288128))) (Checked.append (Checked.append (checkChunk_sound 288256 128 c288256) (checkChunk_sound 288384 128 c288384)) (Checked.append (checkChunk_sound 288512 128 c288512) (checkChunk_sound 288640 128 c288640))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 288768 128 c288768) (checkChunk_sound 288896 128 c288896)) (Checked.append (checkChunk_sound 289024 128 c289024) (checkChunk_sound 289152 128 c289152))) (Checked.append (Checked.append (checkChunk_sound 289280 128 c289280) (checkChunk_sound 289408 128 c289408)) (Checked.append (checkChunk_sound 289536 128 c289536) (checkChunk_sound 289664 128 c289664)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 289792 128 c289792) (checkChunk_sound 289920 128 c289920)) (Checked.append (checkChunk_sound 290048 128 c290048) (checkChunk_sound 290176 128 c290176))) (Checked.append (Checked.append (checkChunk_sound 290304 128 c290304) (checkChunk_sound 290432 128 c290432)) (Checked.append (checkChunk_sound 290560 128 c290560) (checkChunk_sound 290688 128 c290688)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 290816 128 c290816) (checkChunk_sound 290944 128 c290944)) (Checked.append (checkChunk_sound 291072 128 c291072) (checkChunk_sound 291200 128 c291200))) (Checked.append (Checked.append (checkChunk_sound 291328 128 c291328) (checkChunk_sound 291456 128 c291456)) (Checked.append (checkChunk_sound 291584 128 c291584) (checkChunk_sound 291712 128 c291712)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 291840 128 c291840) (checkChunk_sound 291968 128 c291968)) (Checked.append (checkChunk_sound 292096 128 c292096) (checkChunk_sound 292224 128 c292224))) (Checked.append (Checked.append (checkChunk_sound 292352 128 c292352) (checkChunk_sound 292480 128 c292480)) (Checked.append (checkChunk_sound 292608 128 c292608) (checkChunk_sound 292736 128 c292736))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 292864 128 c292864) (checkChunk_sound 292992 128 c292992)) (Checked.append (checkChunk_sound 293120 128 c293120) (checkChunk_sound 293248 128 c293248))) (Checked.append (Checked.append (checkChunk_sound 293376 128 c293376) (checkChunk_sound 293504 128 c293504)) (Checked.append (checkChunk_sound 293632 128 c293632) (checkChunk_sound 293760 128 c293760)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 293888 128 c293888) (checkChunk_sound 294016 128 c294016)) (Checked.append (checkChunk_sound 294144 128 c294144) (checkChunk_sound 294272 128 c294272))) (Checked.append (Checked.append (checkChunk_sound 294400 128 c294400) (checkChunk_sound 294528 128 c294528)) (Checked.append (checkChunk_sound 294656 128 c294656) (checkChunk_sound 294784 128 c294784)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B008
