module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [532480, 540672).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B012
private theorem c532480 : checkChunk 532480 128 = true := by decide +kernel
private theorem c532608 : checkChunk 532608 128 = true := by decide +kernel
private theorem c532736 : checkChunk 532736 128 = true := by decide +kernel
private theorem c532864 : checkChunk 532864 128 = true := by decide +kernel
private theorem c532992 : checkChunk 532992 128 = true := by decide +kernel
private theorem c533120 : checkChunk 533120 128 = true := by decide +kernel
private theorem c533248 : checkChunk 533248 128 = true := by decide +kernel
private theorem c533376 : checkChunk 533376 128 = true := by decide +kernel
private theorem c533504 : checkChunk 533504 128 = true := by decide +kernel
private theorem c533632 : checkChunk 533632 128 = true := by decide +kernel
private theorem c533760 : checkChunk 533760 128 = true := by decide +kernel
private theorem c533888 : checkChunk 533888 128 = true := by decide +kernel
private theorem c534016 : checkChunk 534016 128 = true := by decide +kernel
private theorem c534144 : checkChunk 534144 128 = true := by decide +kernel
private theorem c534272 : checkChunk 534272 128 = true := by decide +kernel
private theorem c534400 : checkChunk 534400 128 = true := by decide +kernel
private theorem c534528 : checkChunk 534528 128 = true := by decide +kernel
private theorem c534656 : checkChunk 534656 128 = true := by decide +kernel
private theorem c534784 : checkChunk 534784 128 = true := by decide +kernel
private theorem c534912 : checkChunk 534912 128 = true := by decide +kernel
private theorem c535040 : checkChunk 535040 128 = true := by decide +kernel
private theorem c535168 : checkChunk 535168 128 = true := by decide +kernel
private theorem c535296 : checkChunk 535296 128 = true := by decide +kernel
private theorem c535424 : checkChunk 535424 128 = true := by decide +kernel
private theorem c535552 : checkChunk 535552 128 = true := by decide +kernel
private theorem c535680 : checkChunk 535680 128 = true := by decide +kernel
private theorem c535808 : checkChunk 535808 128 = true := by decide +kernel
private theorem c535936 : checkChunk 535936 128 = true := by decide +kernel
private theorem c536064 : checkChunk 536064 128 = true := by decide +kernel
private theorem c536192 : checkChunk 536192 128 = true := by decide +kernel
private theorem c536320 : checkChunk 536320 128 = true := by decide +kernel
private theorem c536448 : checkChunk 536448 128 = true := by decide +kernel
private theorem c536576 : checkChunk 536576 128 = true := by decide +kernel
private theorem c536704 : checkChunk 536704 128 = true := by decide +kernel
private theorem c536832 : checkChunk 536832 128 = true := by decide +kernel
private theorem c536960 : checkChunk 536960 128 = true := by decide +kernel
private theorem c537088 : checkChunk 537088 128 = true := by decide +kernel
private theorem c537216 : checkChunk 537216 128 = true := by decide +kernel
private theorem c537344 : checkChunk 537344 128 = true := by decide +kernel
private theorem c537472 : checkChunk 537472 128 = true := by decide +kernel
private theorem c537600 : checkChunk 537600 128 = true := by decide +kernel
private theorem c537728 : checkChunk 537728 128 = true := by decide +kernel
private theorem c537856 : checkChunk 537856 128 = true := by decide +kernel
private theorem c537984 : checkChunk 537984 128 = true := by decide +kernel
private theorem c538112 : checkChunk 538112 128 = true := by decide +kernel
private theorem c538240 : checkChunk 538240 128 = true := by decide +kernel
private theorem c538368 : checkChunk 538368 128 = true := by decide +kernel
private theorem c538496 : checkChunk 538496 128 = true := by decide +kernel
private theorem c538624 : checkChunk 538624 128 = true := by decide +kernel
private theorem c538752 : checkChunk 538752 128 = true := by decide +kernel
private theorem c538880 : checkChunk 538880 128 = true := by decide +kernel
private theorem c539008 : checkChunk 539008 128 = true := by decide +kernel
private theorem c539136 : checkChunk 539136 128 = true := by decide +kernel
private theorem c539264 : checkChunk 539264 128 = true := by decide +kernel
private theorem c539392 : checkChunk 539392 128 = true := by decide +kernel
private theorem c539520 : checkChunk 539520 128 = true := by decide +kernel
private theorem c539648 : checkChunk 539648 128 = true := by decide +kernel
private theorem c539776 : checkChunk 539776 128 = true := by decide +kernel
private theorem c539904 : checkChunk 539904 128 = true := by decide +kernel
private theorem c540032 : checkChunk 540032 128 = true := by decide +kernel
private theorem c540160 : checkChunk 540160 128 = true := by decide +kernel
private theorem c540288 : checkChunk 540288 128 = true := by decide +kernel
private theorem c540416 : checkChunk 540416 128 = true := by decide +kernel
private theorem c540544 : checkChunk 540544 128 = true := by decide +kernel

public theorem checked : Checked 532480 540672 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 532480 128 c532480) (checkChunk_sound 532608 128 c532608)) (Checked.append (checkChunk_sound 532736 128 c532736) (checkChunk_sound 532864 128 c532864))) (Checked.append (Checked.append (checkChunk_sound 532992 128 c532992) (checkChunk_sound 533120 128 c533120)) (Checked.append (checkChunk_sound 533248 128 c533248) (checkChunk_sound 533376 128 c533376)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 533504 128 c533504) (checkChunk_sound 533632 128 c533632)) (Checked.append (checkChunk_sound 533760 128 c533760) (checkChunk_sound 533888 128 c533888))) (Checked.append (Checked.append (checkChunk_sound 534016 128 c534016) (checkChunk_sound 534144 128 c534144)) (Checked.append (checkChunk_sound 534272 128 c534272) (checkChunk_sound 534400 128 c534400))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 534528 128 c534528) (checkChunk_sound 534656 128 c534656)) (Checked.append (checkChunk_sound 534784 128 c534784) (checkChunk_sound 534912 128 c534912))) (Checked.append (Checked.append (checkChunk_sound 535040 128 c535040) (checkChunk_sound 535168 128 c535168)) (Checked.append (checkChunk_sound 535296 128 c535296) (checkChunk_sound 535424 128 c535424)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 535552 128 c535552) (checkChunk_sound 535680 128 c535680)) (Checked.append (checkChunk_sound 535808 128 c535808) (checkChunk_sound 535936 128 c535936))) (Checked.append (Checked.append (checkChunk_sound 536064 128 c536064) (checkChunk_sound 536192 128 c536192)) (Checked.append (checkChunk_sound 536320 128 c536320) (checkChunk_sound 536448 128 c536448)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 536576 128 c536576) (checkChunk_sound 536704 128 c536704)) (Checked.append (checkChunk_sound 536832 128 c536832) (checkChunk_sound 536960 128 c536960))) (Checked.append (Checked.append (checkChunk_sound 537088 128 c537088) (checkChunk_sound 537216 128 c537216)) (Checked.append (checkChunk_sound 537344 128 c537344) (checkChunk_sound 537472 128 c537472)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 537600 128 c537600) (checkChunk_sound 537728 128 c537728)) (Checked.append (checkChunk_sound 537856 128 c537856) (checkChunk_sound 537984 128 c537984))) (Checked.append (Checked.append (checkChunk_sound 538112 128 c538112) (checkChunk_sound 538240 128 c538240)) (Checked.append (checkChunk_sound 538368 128 c538368) (checkChunk_sound 538496 128 c538496))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 538624 128 c538624) (checkChunk_sound 538752 128 c538752)) (Checked.append (checkChunk_sound 538880 128 c538880) (checkChunk_sound 539008 128 c539008))) (Checked.append (Checked.append (checkChunk_sound 539136 128 c539136) (checkChunk_sound 539264 128 c539264)) (Checked.append (checkChunk_sound 539392 128 c539392) (checkChunk_sound 539520 128 c539520)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 539648 128 c539648) (checkChunk_sound 539776 128 c539776)) (Checked.append (checkChunk_sound 539904 128 c539904) (checkChunk_sound 540032 128 c540032))) (Checked.append (Checked.append (checkChunk_sound 540160 128 c540160) (checkChunk_sound 540288 128 c540288)) (Checked.append (checkChunk_sound 540416 128 c540416) (checkChunk_sound 540544 128 c540544)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B012
