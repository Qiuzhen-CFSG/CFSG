module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [720896, 729088).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B009
private theorem c720896 : checkChunk 720896 128 = true := by decide +kernel
private theorem c721024 : checkChunk 721024 128 = true := by decide +kernel
private theorem c721152 : checkChunk 721152 128 = true := by decide +kernel
private theorem c721280 : checkChunk 721280 128 = true := by decide +kernel
private theorem c721408 : checkChunk 721408 128 = true := by decide +kernel
private theorem c721536 : checkChunk 721536 128 = true := by decide +kernel
private theorem c721664 : checkChunk 721664 128 = true := by decide +kernel
private theorem c721792 : checkChunk 721792 128 = true := by decide +kernel
private theorem c721920 : checkChunk 721920 128 = true := by decide +kernel
private theorem c722048 : checkChunk 722048 128 = true := by decide +kernel
private theorem c722176 : checkChunk 722176 128 = true := by decide +kernel
private theorem c722304 : checkChunk 722304 128 = true := by decide +kernel
private theorem c722432 : checkChunk 722432 128 = true := by decide +kernel
private theorem c722560 : checkChunk 722560 128 = true := by decide +kernel
private theorem c722688 : checkChunk 722688 128 = true := by decide +kernel
private theorem c722816 : checkChunk 722816 128 = true := by decide +kernel
private theorem c722944 : checkChunk 722944 128 = true := by decide +kernel
private theorem c723072 : checkChunk 723072 128 = true := by decide +kernel
private theorem c723200 : checkChunk 723200 128 = true := by decide +kernel
private theorem c723328 : checkChunk 723328 128 = true := by decide +kernel
private theorem c723456 : checkChunk 723456 128 = true := by decide +kernel
private theorem c723584 : checkChunk 723584 128 = true := by decide +kernel
private theorem c723712 : checkChunk 723712 128 = true := by decide +kernel
private theorem c723840 : checkChunk 723840 128 = true := by decide +kernel
private theorem c723968 : checkChunk 723968 128 = true := by decide +kernel
private theorem c724096 : checkChunk 724096 128 = true := by decide +kernel
private theorem c724224 : checkChunk 724224 128 = true := by decide +kernel
private theorem c724352 : checkChunk 724352 128 = true := by decide +kernel
private theorem c724480 : checkChunk 724480 128 = true := by decide +kernel
private theorem c724608 : checkChunk 724608 128 = true := by decide +kernel
private theorem c724736 : checkChunk 724736 128 = true := by decide +kernel
private theorem c724864 : checkChunk 724864 128 = true := by decide +kernel
private theorem c724992 : checkChunk 724992 128 = true := by decide +kernel
private theorem c725120 : checkChunk 725120 128 = true := by decide +kernel
private theorem c725248 : checkChunk 725248 128 = true := by decide +kernel
private theorem c725376 : checkChunk 725376 128 = true := by decide +kernel
private theorem c725504 : checkChunk 725504 128 = true := by decide +kernel
private theorem c725632 : checkChunk 725632 128 = true := by decide +kernel
private theorem c725760 : checkChunk 725760 128 = true := by decide +kernel
private theorem c725888 : checkChunk 725888 128 = true := by decide +kernel
private theorem c726016 : checkChunk 726016 128 = true := by decide +kernel
private theorem c726144 : checkChunk 726144 128 = true := by decide +kernel
private theorem c726272 : checkChunk 726272 128 = true := by decide +kernel
private theorem c726400 : checkChunk 726400 128 = true := by decide +kernel
private theorem c726528 : checkChunk 726528 128 = true := by decide +kernel
private theorem c726656 : checkChunk 726656 128 = true := by decide +kernel
private theorem c726784 : checkChunk 726784 128 = true := by decide +kernel
private theorem c726912 : checkChunk 726912 128 = true := by decide +kernel
private theorem c727040 : checkChunk 727040 128 = true := by decide +kernel
private theorem c727168 : checkChunk 727168 128 = true := by decide +kernel
private theorem c727296 : checkChunk 727296 128 = true := by decide +kernel
private theorem c727424 : checkChunk 727424 128 = true := by decide +kernel
private theorem c727552 : checkChunk 727552 128 = true := by decide +kernel
private theorem c727680 : checkChunk 727680 128 = true := by decide +kernel
private theorem c727808 : checkChunk 727808 128 = true := by decide +kernel
private theorem c727936 : checkChunk 727936 128 = true := by decide +kernel
private theorem c728064 : checkChunk 728064 128 = true := by decide +kernel
private theorem c728192 : checkChunk 728192 128 = true := by decide +kernel
private theorem c728320 : checkChunk 728320 128 = true := by decide +kernel
private theorem c728448 : checkChunk 728448 128 = true := by decide +kernel
private theorem c728576 : checkChunk 728576 128 = true := by decide +kernel
private theorem c728704 : checkChunk 728704 128 = true := by decide +kernel
private theorem c728832 : checkChunk 728832 128 = true := by decide +kernel
private theorem c728960 : checkChunk 728960 128 = true := by decide +kernel

public theorem checked : Checked 720896 729088 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 720896 128 c720896) (checkChunk_sound 721024 128 c721024)) (Checked.append (checkChunk_sound 721152 128 c721152) (checkChunk_sound 721280 128 c721280))) (Checked.append (Checked.append (checkChunk_sound 721408 128 c721408) (checkChunk_sound 721536 128 c721536)) (Checked.append (checkChunk_sound 721664 128 c721664) (checkChunk_sound 721792 128 c721792)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 721920 128 c721920) (checkChunk_sound 722048 128 c722048)) (Checked.append (checkChunk_sound 722176 128 c722176) (checkChunk_sound 722304 128 c722304))) (Checked.append (Checked.append (checkChunk_sound 722432 128 c722432) (checkChunk_sound 722560 128 c722560)) (Checked.append (checkChunk_sound 722688 128 c722688) (checkChunk_sound 722816 128 c722816))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 722944 128 c722944) (checkChunk_sound 723072 128 c723072)) (Checked.append (checkChunk_sound 723200 128 c723200) (checkChunk_sound 723328 128 c723328))) (Checked.append (Checked.append (checkChunk_sound 723456 128 c723456) (checkChunk_sound 723584 128 c723584)) (Checked.append (checkChunk_sound 723712 128 c723712) (checkChunk_sound 723840 128 c723840)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 723968 128 c723968) (checkChunk_sound 724096 128 c724096)) (Checked.append (checkChunk_sound 724224 128 c724224) (checkChunk_sound 724352 128 c724352))) (Checked.append (Checked.append (checkChunk_sound 724480 128 c724480) (checkChunk_sound 724608 128 c724608)) (Checked.append (checkChunk_sound 724736 128 c724736) (checkChunk_sound 724864 128 c724864)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 724992 128 c724992) (checkChunk_sound 725120 128 c725120)) (Checked.append (checkChunk_sound 725248 128 c725248) (checkChunk_sound 725376 128 c725376))) (Checked.append (Checked.append (checkChunk_sound 725504 128 c725504) (checkChunk_sound 725632 128 c725632)) (Checked.append (checkChunk_sound 725760 128 c725760) (checkChunk_sound 725888 128 c725888)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 726016 128 c726016) (checkChunk_sound 726144 128 c726144)) (Checked.append (checkChunk_sound 726272 128 c726272) (checkChunk_sound 726400 128 c726400))) (Checked.append (Checked.append (checkChunk_sound 726528 128 c726528) (checkChunk_sound 726656 128 c726656)) (Checked.append (checkChunk_sound 726784 128 c726784) (checkChunk_sound 726912 128 c726912))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 727040 128 c727040) (checkChunk_sound 727168 128 c727168)) (Checked.append (checkChunk_sound 727296 128 c727296) (checkChunk_sound 727424 128 c727424))) (Checked.append (Checked.append (checkChunk_sound 727552 128 c727552) (checkChunk_sound 727680 128 c727680)) (Checked.append (checkChunk_sound 727808 128 c727808) (checkChunk_sound 727936 128 c727936)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 728064 128 c728064) (checkChunk_sound 728192 128 c728192)) (Checked.append (checkChunk_sound 728320 128 c728320) (checkChunk_sound 728448 128 c728448))) (Checked.append (Checked.append (checkChunk_sound 728576 128 c728576) (checkChunk_sound 728704 128 c728704)) (Checked.append (checkChunk_sound 728832 128 c728832) (checkChunk_sound 728960 128 c728960)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B009
