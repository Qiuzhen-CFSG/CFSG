module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [368640, 376832).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B018
private theorem c368640 : checkChunk 368640 128 = true := by decide +kernel
private theorem c368768 : checkChunk 368768 128 = true := by decide +kernel
private theorem c368896 : checkChunk 368896 128 = true := by decide +kernel
private theorem c369024 : checkChunk 369024 128 = true := by decide +kernel
private theorem c369152 : checkChunk 369152 128 = true := by decide +kernel
private theorem c369280 : checkChunk 369280 128 = true := by decide +kernel
private theorem c369408 : checkChunk 369408 128 = true := by decide +kernel
private theorem c369536 : checkChunk 369536 128 = true := by decide +kernel
private theorem c369664 : checkChunk 369664 128 = true := by decide +kernel
private theorem c369792 : checkChunk 369792 128 = true := by decide +kernel
private theorem c369920 : checkChunk 369920 128 = true := by decide +kernel
private theorem c370048 : checkChunk 370048 128 = true := by decide +kernel
private theorem c370176 : checkChunk 370176 128 = true := by decide +kernel
private theorem c370304 : checkChunk 370304 128 = true := by decide +kernel
private theorem c370432 : checkChunk 370432 128 = true := by decide +kernel
private theorem c370560 : checkChunk 370560 128 = true := by decide +kernel
private theorem c370688 : checkChunk 370688 128 = true := by decide +kernel
private theorem c370816 : checkChunk 370816 128 = true := by decide +kernel
private theorem c370944 : checkChunk 370944 128 = true := by decide +kernel
private theorem c371072 : checkChunk 371072 128 = true := by decide +kernel
private theorem c371200 : checkChunk 371200 128 = true := by decide +kernel
private theorem c371328 : checkChunk 371328 128 = true := by decide +kernel
private theorem c371456 : checkChunk 371456 128 = true := by decide +kernel
private theorem c371584 : checkChunk 371584 128 = true := by decide +kernel
private theorem c371712 : checkChunk 371712 128 = true := by decide +kernel
private theorem c371840 : checkChunk 371840 128 = true := by decide +kernel
private theorem c371968 : checkChunk 371968 128 = true := by decide +kernel
private theorem c372096 : checkChunk 372096 128 = true := by decide +kernel
private theorem c372224 : checkChunk 372224 128 = true := by decide +kernel
private theorem c372352 : checkChunk 372352 128 = true := by decide +kernel
private theorem c372480 : checkChunk 372480 128 = true := by decide +kernel
private theorem c372608 : checkChunk 372608 128 = true := by decide +kernel
private theorem c372736 : checkChunk 372736 128 = true := by decide +kernel
private theorem c372864 : checkChunk 372864 128 = true := by decide +kernel
private theorem c372992 : checkChunk 372992 128 = true := by decide +kernel
private theorem c373120 : checkChunk 373120 128 = true := by decide +kernel
private theorem c373248 : checkChunk 373248 128 = true := by decide +kernel
private theorem c373376 : checkChunk 373376 128 = true := by decide +kernel
private theorem c373504 : checkChunk 373504 128 = true := by decide +kernel
private theorem c373632 : checkChunk 373632 128 = true := by decide +kernel
private theorem c373760 : checkChunk 373760 128 = true := by decide +kernel
private theorem c373888 : checkChunk 373888 128 = true := by decide +kernel
private theorem c374016 : checkChunk 374016 128 = true := by decide +kernel
private theorem c374144 : checkChunk 374144 128 = true := by decide +kernel
private theorem c374272 : checkChunk 374272 128 = true := by decide +kernel
private theorem c374400 : checkChunk 374400 128 = true := by decide +kernel
private theorem c374528 : checkChunk 374528 128 = true := by decide +kernel
private theorem c374656 : checkChunk 374656 128 = true := by decide +kernel
private theorem c374784 : checkChunk 374784 128 = true := by decide +kernel
private theorem c374912 : checkChunk 374912 128 = true := by decide +kernel
private theorem c375040 : checkChunk 375040 128 = true := by decide +kernel
private theorem c375168 : checkChunk 375168 128 = true := by decide +kernel
private theorem c375296 : checkChunk 375296 128 = true := by decide +kernel
private theorem c375424 : checkChunk 375424 128 = true := by decide +kernel
private theorem c375552 : checkChunk 375552 128 = true := by decide +kernel
private theorem c375680 : checkChunk 375680 128 = true := by decide +kernel
private theorem c375808 : checkChunk 375808 128 = true := by decide +kernel
private theorem c375936 : checkChunk 375936 128 = true := by decide +kernel
private theorem c376064 : checkChunk 376064 128 = true := by decide +kernel
private theorem c376192 : checkChunk 376192 128 = true := by decide +kernel
private theorem c376320 : checkChunk 376320 128 = true := by decide +kernel
private theorem c376448 : checkChunk 376448 128 = true := by decide +kernel
private theorem c376576 : checkChunk 376576 128 = true := by decide +kernel
private theorem c376704 : checkChunk 376704 128 = true := by decide +kernel

public theorem checked : Checked 368640 376832 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 368640 128 c368640) (checkChunk_sound 368768 128 c368768)) (Checked.append (checkChunk_sound 368896 128 c368896) (checkChunk_sound 369024 128 c369024))) (Checked.append (Checked.append (checkChunk_sound 369152 128 c369152) (checkChunk_sound 369280 128 c369280)) (Checked.append (checkChunk_sound 369408 128 c369408) (checkChunk_sound 369536 128 c369536)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 369664 128 c369664) (checkChunk_sound 369792 128 c369792)) (Checked.append (checkChunk_sound 369920 128 c369920) (checkChunk_sound 370048 128 c370048))) (Checked.append (Checked.append (checkChunk_sound 370176 128 c370176) (checkChunk_sound 370304 128 c370304)) (Checked.append (checkChunk_sound 370432 128 c370432) (checkChunk_sound 370560 128 c370560))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 370688 128 c370688) (checkChunk_sound 370816 128 c370816)) (Checked.append (checkChunk_sound 370944 128 c370944) (checkChunk_sound 371072 128 c371072))) (Checked.append (Checked.append (checkChunk_sound 371200 128 c371200) (checkChunk_sound 371328 128 c371328)) (Checked.append (checkChunk_sound 371456 128 c371456) (checkChunk_sound 371584 128 c371584)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 371712 128 c371712) (checkChunk_sound 371840 128 c371840)) (Checked.append (checkChunk_sound 371968 128 c371968) (checkChunk_sound 372096 128 c372096))) (Checked.append (Checked.append (checkChunk_sound 372224 128 c372224) (checkChunk_sound 372352 128 c372352)) (Checked.append (checkChunk_sound 372480 128 c372480) (checkChunk_sound 372608 128 c372608)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 372736 128 c372736) (checkChunk_sound 372864 128 c372864)) (Checked.append (checkChunk_sound 372992 128 c372992) (checkChunk_sound 373120 128 c373120))) (Checked.append (Checked.append (checkChunk_sound 373248 128 c373248) (checkChunk_sound 373376 128 c373376)) (Checked.append (checkChunk_sound 373504 128 c373504) (checkChunk_sound 373632 128 c373632)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 373760 128 c373760) (checkChunk_sound 373888 128 c373888)) (Checked.append (checkChunk_sound 374016 128 c374016) (checkChunk_sound 374144 128 c374144))) (Checked.append (Checked.append (checkChunk_sound 374272 128 c374272) (checkChunk_sound 374400 128 c374400)) (Checked.append (checkChunk_sound 374528 128 c374528) (checkChunk_sound 374656 128 c374656))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 374784 128 c374784) (checkChunk_sound 374912 128 c374912)) (Checked.append (checkChunk_sound 375040 128 c375040) (checkChunk_sound 375168 128 c375168))) (Checked.append (Checked.append (checkChunk_sound 375296 128 c375296) (checkChunk_sound 375424 128 c375424)) (Checked.append (checkChunk_sound 375552 128 c375552) (checkChunk_sound 375680 128 c375680)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 375808 128 c375808) (checkChunk_sound 375936 128 c375936)) (Checked.append (checkChunk_sound 376064 128 c376064) (checkChunk_sound 376192 128 c376192))) (Checked.append (Checked.append (checkChunk_sound 376320 128 c376320) (checkChunk_sound 376448 128 c376448)) (Checked.append (checkChunk_sound 376576 128 c376576) (checkChunk_sound 376704 128 c376704)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B018
