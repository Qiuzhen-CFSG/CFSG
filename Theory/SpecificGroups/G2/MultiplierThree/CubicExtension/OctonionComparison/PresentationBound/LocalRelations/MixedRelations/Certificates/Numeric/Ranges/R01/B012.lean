module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [319488, 327680).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B012
private theorem c319488 : checkChunk 319488 128 = true := by decide +kernel
private theorem c319616 : checkChunk 319616 128 = true := by decide +kernel
private theorem c319744 : checkChunk 319744 128 = true := by decide +kernel
private theorem c319872 : checkChunk 319872 128 = true := by decide +kernel
private theorem c320000 : checkChunk 320000 128 = true := by decide +kernel
private theorem c320128 : checkChunk 320128 128 = true := by decide +kernel
private theorem c320256 : checkChunk 320256 128 = true := by decide +kernel
private theorem c320384 : checkChunk 320384 128 = true := by decide +kernel
private theorem c320512 : checkChunk 320512 128 = true := by decide +kernel
private theorem c320640 : checkChunk 320640 128 = true := by decide +kernel
private theorem c320768 : checkChunk 320768 128 = true := by decide +kernel
private theorem c320896 : checkChunk 320896 128 = true := by decide +kernel
private theorem c321024 : checkChunk 321024 128 = true := by decide +kernel
private theorem c321152 : checkChunk 321152 128 = true := by decide +kernel
private theorem c321280 : checkChunk 321280 128 = true := by decide +kernel
private theorem c321408 : checkChunk 321408 128 = true := by decide +kernel
private theorem c321536 : checkChunk 321536 128 = true := by decide +kernel
private theorem c321664 : checkChunk 321664 128 = true := by decide +kernel
private theorem c321792 : checkChunk 321792 128 = true := by decide +kernel
private theorem c321920 : checkChunk 321920 128 = true := by decide +kernel
private theorem c322048 : checkChunk 322048 128 = true := by decide +kernel
private theorem c322176 : checkChunk 322176 128 = true := by decide +kernel
private theorem c322304 : checkChunk 322304 128 = true := by decide +kernel
private theorem c322432 : checkChunk 322432 128 = true := by decide +kernel
private theorem c322560 : checkChunk 322560 128 = true := by decide +kernel
private theorem c322688 : checkChunk 322688 128 = true := by decide +kernel
private theorem c322816 : checkChunk 322816 128 = true := by decide +kernel
private theorem c322944 : checkChunk 322944 128 = true := by decide +kernel
private theorem c323072 : checkChunk 323072 128 = true := by decide +kernel
private theorem c323200 : checkChunk 323200 128 = true := by decide +kernel
private theorem c323328 : checkChunk 323328 128 = true := by decide +kernel
private theorem c323456 : checkChunk 323456 128 = true := by decide +kernel
private theorem c323584 : checkChunk 323584 128 = true := by decide +kernel
private theorem c323712 : checkChunk 323712 128 = true := by decide +kernel
private theorem c323840 : checkChunk 323840 128 = true := by decide +kernel
private theorem c323968 : checkChunk 323968 128 = true := by decide +kernel
private theorem c324096 : checkChunk 324096 128 = true := by decide +kernel
private theorem c324224 : checkChunk 324224 128 = true := by decide +kernel
private theorem c324352 : checkChunk 324352 128 = true := by decide +kernel
private theorem c324480 : checkChunk 324480 128 = true := by decide +kernel
private theorem c324608 : checkChunk 324608 128 = true := by decide +kernel
private theorem c324736 : checkChunk 324736 128 = true := by decide +kernel
private theorem c324864 : checkChunk 324864 128 = true := by decide +kernel
private theorem c324992 : checkChunk 324992 128 = true := by decide +kernel
private theorem c325120 : checkChunk 325120 128 = true := by decide +kernel
private theorem c325248 : checkChunk 325248 128 = true := by decide +kernel
private theorem c325376 : checkChunk 325376 128 = true := by decide +kernel
private theorem c325504 : checkChunk 325504 128 = true := by decide +kernel
private theorem c325632 : checkChunk 325632 128 = true := by decide +kernel
private theorem c325760 : checkChunk 325760 128 = true := by decide +kernel
private theorem c325888 : checkChunk 325888 128 = true := by decide +kernel
private theorem c326016 : checkChunk 326016 128 = true := by decide +kernel
private theorem c326144 : checkChunk 326144 128 = true := by decide +kernel
private theorem c326272 : checkChunk 326272 128 = true := by decide +kernel
private theorem c326400 : checkChunk 326400 128 = true := by decide +kernel
private theorem c326528 : checkChunk 326528 128 = true := by decide +kernel
private theorem c326656 : checkChunk 326656 128 = true := by decide +kernel
private theorem c326784 : checkChunk 326784 128 = true := by decide +kernel
private theorem c326912 : checkChunk 326912 128 = true := by decide +kernel
private theorem c327040 : checkChunk 327040 128 = true := by decide +kernel
private theorem c327168 : checkChunk 327168 128 = true := by decide +kernel
private theorem c327296 : checkChunk 327296 128 = true := by decide +kernel
private theorem c327424 : checkChunk 327424 128 = true := by decide +kernel
private theorem c327552 : checkChunk 327552 128 = true := by decide +kernel

public theorem checked : Checked 319488 327680 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 319488 128 c319488) (checkChunk_sound 319616 128 c319616)) (Checked.append (checkChunk_sound 319744 128 c319744) (checkChunk_sound 319872 128 c319872))) (Checked.append (Checked.append (checkChunk_sound 320000 128 c320000) (checkChunk_sound 320128 128 c320128)) (Checked.append (checkChunk_sound 320256 128 c320256) (checkChunk_sound 320384 128 c320384)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 320512 128 c320512) (checkChunk_sound 320640 128 c320640)) (Checked.append (checkChunk_sound 320768 128 c320768) (checkChunk_sound 320896 128 c320896))) (Checked.append (Checked.append (checkChunk_sound 321024 128 c321024) (checkChunk_sound 321152 128 c321152)) (Checked.append (checkChunk_sound 321280 128 c321280) (checkChunk_sound 321408 128 c321408))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 321536 128 c321536) (checkChunk_sound 321664 128 c321664)) (Checked.append (checkChunk_sound 321792 128 c321792) (checkChunk_sound 321920 128 c321920))) (Checked.append (Checked.append (checkChunk_sound 322048 128 c322048) (checkChunk_sound 322176 128 c322176)) (Checked.append (checkChunk_sound 322304 128 c322304) (checkChunk_sound 322432 128 c322432)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 322560 128 c322560) (checkChunk_sound 322688 128 c322688)) (Checked.append (checkChunk_sound 322816 128 c322816) (checkChunk_sound 322944 128 c322944))) (Checked.append (Checked.append (checkChunk_sound 323072 128 c323072) (checkChunk_sound 323200 128 c323200)) (Checked.append (checkChunk_sound 323328 128 c323328) (checkChunk_sound 323456 128 c323456)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 323584 128 c323584) (checkChunk_sound 323712 128 c323712)) (Checked.append (checkChunk_sound 323840 128 c323840) (checkChunk_sound 323968 128 c323968))) (Checked.append (Checked.append (checkChunk_sound 324096 128 c324096) (checkChunk_sound 324224 128 c324224)) (Checked.append (checkChunk_sound 324352 128 c324352) (checkChunk_sound 324480 128 c324480)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 324608 128 c324608) (checkChunk_sound 324736 128 c324736)) (Checked.append (checkChunk_sound 324864 128 c324864) (checkChunk_sound 324992 128 c324992))) (Checked.append (Checked.append (checkChunk_sound 325120 128 c325120) (checkChunk_sound 325248 128 c325248)) (Checked.append (checkChunk_sound 325376 128 c325376) (checkChunk_sound 325504 128 c325504))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 325632 128 c325632) (checkChunk_sound 325760 128 c325760)) (Checked.append (checkChunk_sound 325888 128 c325888) (checkChunk_sound 326016 128 c326016))) (Checked.append (Checked.append (checkChunk_sound 326144 128 c326144) (checkChunk_sound 326272 128 c326272)) (Checked.append (checkChunk_sound 326400 128 c326400) (checkChunk_sound 326528 128 c326528)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 326656 128 c326656) (checkChunk_sound 326784 128 c326784)) (Checked.append (checkChunk_sound 326912 128 c326912) (checkChunk_sound 327040 128 c327040))) (Checked.append (Checked.append (checkChunk_sound 327168 128 c327168) (checkChunk_sound 327296 128 c327296)) (Checked.append (checkChunk_sound 327424 128 c327424) (checkChunk_sound 327552 128 c327552)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B012
