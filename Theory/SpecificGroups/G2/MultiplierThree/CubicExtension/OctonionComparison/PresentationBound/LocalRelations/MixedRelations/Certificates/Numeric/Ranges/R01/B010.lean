module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [303104, 311296).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B010
private theorem c303104 : checkChunk 303104 128 = true := by decide +kernel
private theorem c303232 : checkChunk 303232 128 = true := by decide +kernel
private theorem c303360 : checkChunk 303360 128 = true := by decide +kernel
private theorem c303488 : checkChunk 303488 128 = true := by decide +kernel
private theorem c303616 : checkChunk 303616 128 = true := by decide +kernel
private theorem c303744 : checkChunk 303744 128 = true := by decide +kernel
private theorem c303872 : checkChunk 303872 128 = true := by decide +kernel
private theorem c304000 : checkChunk 304000 128 = true := by decide +kernel
private theorem c304128 : checkChunk 304128 128 = true := by decide +kernel
private theorem c304256 : checkChunk 304256 128 = true := by decide +kernel
private theorem c304384 : checkChunk 304384 128 = true := by decide +kernel
private theorem c304512 : checkChunk 304512 128 = true := by decide +kernel
private theorem c304640 : checkChunk 304640 128 = true := by decide +kernel
private theorem c304768 : checkChunk 304768 128 = true := by decide +kernel
private theorem c304896 : checkChunk 304896 128 = true := by decide +kernel
private theorem c305024 : checkChunk 305024 128 = true := by decide +kernel
private theorem c305152 : checkChunk 305152 128 = true := by decide +kernel
private theorem c305280 : checkChunk 305280 128 = true := by decide +kernel
private theorem c305408 : checkChunk 305408 128 = true := by decide +kernel
private theorem c305536 : checkChunk 305536 128 = true := by decide +kernel
private theorem c305664 : checkChunk 305664 128 = true := by decide +kernel
private theorem c305792 : checkChunk 305792 128 = true := by decide +kernel
private theorem c305920 : checkChunk 305920 128 = true := by decide +kernel
private theorem c306048 : checkChunk 306048 128 = true := by decide +kernel
private theorem c306176 : checkChunk 306176 128 = true := by decide +kernel
private theorem c306304 : checkChunk 306304 128 = true := by decide +kernel
private theorem c306432 : checkChunk 306432 128 = true := by decide +kernel
private theorem c306560 : checkChunk 306560 128 = true := by decide +kernel
private theorem c306688 : checkChunk 306688 128 = true := by decide +kernel
private theorem c306816 : checkChunk 306816 128 = true := by decide +kernel
private theorem c306944 : checkChunk 306944 128 = true := by decide +kernel
private theorem c307072 : checkChunk 307072 128 = true := by decide +kernel
private theorem c307200 : checkChunk 307200 128 = true := by decide +kernel
private theorem c307328 : checkChunk 307328 128 = true := by decide +kernel
private theorem c307456 : checkChunk 307456 128 = true := by decide +kernel
private theorem c307584 : checkChunk 307584 128 = true := by decide +kernel
private theorem c307712 : checkChunk 307712 128 = true := by decide +kernel
private theorem c307840 : checkChunk 307840 128 = true := by decide +kernel
private theorem c307968 : checkChunk 307968 128 = true := by decide +kernel
private theorem c308096 : checkChunk 308096 128 = true := by decide +kernel
private theorem c308224 : checkChunk 308224 128 = true := by decide +kernel
private theorem c308352 : checkChunk 308352 128 = true := by decide +kernel
private theorem c308480 : checkChunk 308480 128 = true := by decide +kernel
private theorem c308608 : checkChunk 308608 128 = true := by decide +kernel
private theorem c308736 : checkChunk 308736 128 = true := by decide +kernel
private theorem c308864 : checkChunk 308864 128 = true := by decide +kernel
private theorem c308992 : checkChunk 308992 128 = true := by decide +kernel
private theorem c309120 : checkChunk 309120 128 = true := by decide +kernel
private theorem c309248 : checkChunk 309248 128 = true := by decide +kernel
private theorem c309376 : checkChunk 309376 128 = true := by decide +kernel
private theorem c309504 : checkChunk 309504 128 = true := by decide +kernel
private theorem c309632 : checkChunk 309632 128 = true := by decide +kernel
private theorem c309760 : checkChunk 309760 128 = true := by decide +kernel
private theorem c309888 : checkChunk 309888 128 = true := by decide +kernel
private theorem c310016 : checkChunk 310016 128 = true := by decide +kernel
private theorem c310144 : checkChunk 310144 128 = true := by decide +kernel
private theorem c310272 : checkChunk 310272 128 = true := by decide +kernel
private theorem c310400 : checkChunk 310400 128 = true := by decide +kernel
private theorem c310528 : checkChunk 310528 128 = true := by decide +kernel
private theorem c310656 : checkChunk 310656 128 = true := by decide +kernel
private theorem c310784 : checkChunk 310784 128 = true := by decide +kernel
private theorem c310912 : checkChunk 310912 128 = true := by decide +kernel
private theorem c311040 : checkChunk 311040 128 = true := by decide +kernel
private theorem c311168 : checkChunk 311168 128 = true := by decide +kernel

public theorem checked : Checked 303104 311296 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 303104 128 c303104) (checkChunk_sound 303232 128 c303232)) (Checked.append (checkChunk_sound 303360 128 c303360) (checkChunk_sound 303488 128 c303488))) (Checked.append (Checked.append (checkChunk_sound 303616 128 c303616) (checkChunk_sound 303744 128 c303744)) (Checked.append (checkChunk_sound 303872 128 c303872) (checkChunk_sound 304000 128 c304000)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 304128 128 c304128) (checkChunk_sound 304256 128 c304256)) (Checked.append (checkChunk_sound 304384 128 c304384) (checkChunk_sound 304512 128 c304512))) (Checked.append (Checked.append (checkChunk_sound 304640 128 c304640) (checkChunk_sound 304768 128 c304768)) (Checked.append (checkChunk_sound 304896 128 c304896) (checkChunk_sound 305024 128 c305024))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 305152 128 c305152) (checkChunk_sound 305280 128 c305280)) (Checked.append (checkChunk_sound 305408 128 c305408) (checkChunk_sound 305536 128 c305536))) (Checked.append (Checked.append (checkChunk_sound 305664 128 c305664) (checkChunk_sound 305792 128 c305792)) (Checked.append (checkChunk_sound 305920 128 c305920) (checkChunk_sound 306048 128 c306048)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 306176 128 c306176) (checkChunk_sound 306304 128 c306304)) (Checked.append (checkChunk_sound 306432 128 c306432) (checkChunk_sound 306560 128 c306560))) (Checked.append (Checked.append (checkChunk_sound 306688 128 c306688) (checkChunk_sound 306816 128 c306816)) (Checked.append (checkChunk_sound 306944 128 c306944) (checkChunk_sound 307072 128 c307072)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 307200 128 c307200) (checkChunk_sound 307328 128 c307328)) (Checked.append (checkChunk_sound 307456 128 c307456) (checkChunk_sound 307584 128 c307584))) (Checked.append (Checked.append (checkChunk_sound 307712 128 c307712) (checkChunk_sound 307840 128 c307840)) (Checked.append (checkChunk_sound 307968 128 c307968) (checkChunk_sound 308096 128 c308096)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 308224 128 c308224) (checkChunk_sound 308352 128 c308352)) (Checked.append (checkChunk_sound 308480 128 c308480) (checkChunk_sound 308608 128 c308608))) (Checked.append (Checked.append (checkChunk_sound 308736 128 c308736) (checkChunk_sound 308864 128 c308864)) (Checked.append (checkChunk_sound 308992 128 c308992) (checkChunk_sound 309120 128 c309120))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 309248 128 c309248) (checkChunk_sound 309376 128 c309376)) (Checked.append (checkChunk_sound 309504 128 c309504) (checkChunk_sound 309632 128 c309632))) (Checked.append (Checked.append (checkChunk_sound 309760 128 c309760) (checkChunk_sound 309888 128 c309888)) (Checked.append (checkChunk_sound 310016 128 c310016) (checkChunk_sound 310144 128 c310144)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 310272 128 c310272) (checkChunk_sound 310400 128 c310400)) (Checked.append (checkChunk_sound 310528 128 c310528) (checkChunk_sound 310656 128 c310656))) (Checked.append (Checked.append (checkChunk_sound 310784 128 c310784) (checkChunk_sound 310912 128 c310912)) (Checked.append (checkChunk_sound 311040 128 c311040) (checkChunk_sound 311168 128 c311168)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B010
