module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [253952, 262144).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B004
private theorem c253952 : checkChunk 253952 128 = true := by decide +kernel
private theorem c254080 : checkChunk 254080 128 = true := by decide +kernel
private theorem c254208 : checkChunk 254208 128 = true := by decide +kernel
private theorem c254336 : checkChunk 254336 128 = true := by decide +kernel
private theorem c254464 : checkChunk 254464 128 = true := by decide +kernel
private theorem c254592 : checkChunk 254592 128 = true := by decide +kernel
private theorem c254720 : checkChunk 254720 128 = true := by decide +kernel
private theorem c254848 : checkChunk 254848 128 = true := by decide +kernel
private theorem c254976 : checkChunk 254976 128 = true := by decide +kernel
private theorem c255104 : checkChunk 255104 128 = true := by decide +kernel
private theorem c255232 : checkChunk 255232 128 = true := by decide +kernel
private theorem c255360 : checkChunk 255360 128 = true := by decide +kernel
private theorem c255488 : checkChunk 255488 128 = true := by decide +kernel
private theorem c255616 : checkChunk 255616 128 = true := by decide +kernel
private theorem c255744 : checkChunk 255744 128 = true := by decide +kernel
private theorem c255872 : checkChunk 255872 128 = true := by decide +kernel
private theorem c256000 : checkChunk 256000 128 = true := by decide +kernel
private theorem c256128 : checkChunk 256128 128 = true := by decide +kernel
private theorem c256256 : checkChunk 256256 128 = true := by decide +kernel
private theorem c256384 : checkChunk 256384 128 = true := by decide +kernel
private theorem c256512 : checkChunk 256512 128 = true := by decide +kernel
private theorem c256640 : checkChunk 256640 128 = true := by decide +kernel
private theorem c256768 : checkChunk 256768 128 = true := by decide +kernel
private theorem c256896 : checkChunk 256896 128 = true := by decide +kernel
private theorem c257024 : checkChunk 257024 128 = true := by decide +kernel
private theorem c257152 : checkChunk 257152 128 = true := by decide +kernel
private theorem c257280 : checkChunk 257280 128 = true := by decide +kernel
private theorem c257408 : checkChunk 257408 128 = true := by decide +kernel
private theorem c257536 : checkChunk 257536 128 = true := by decide +kernel
private theorem c257664 : checkChunk 257664 128 = true := by decide +kernel
private theorem c257792 : checkChunk 257792 128 = true := by decide +kernel
private theorem c257920 : checkChunk 257920 128 = true := by decide +kernel
private theorem c258048 : checkChunk 258048 128 = true := by decide +kernel
private theorem c258176 : checkChunk 258176 128 = true := by decide +kernel
private theorem c258304 : checkChunk 258304 128 = true := by decide +kernel
private theorem c258432 : checkChunk 258432 128 = true := by decide +kernel
private theorem c258560 : checkChunk 258560 128 = true := by decide +kernel
private theorem c258688 : checkChunk 258688 128 = true := by decide +kernel
private theorem c258816 : checkChunk 258816 128 = true := by decide +kernel
private theorem c258944 : checkChunk 258944 128 = true := by decide +kernel
private theorem c259072 : checkChunk 259072 128 = true := by decide +kernel
private theorem c259200 : checkChunk 259200 128 = true := by decide +kernel
private theorem c259328 : checkChunk 259328 128 = true := by decide +kernel
private theorem c259456 : checkChunk 259456 128 = true := by decide +kernel
private theorem c259584 : checkChunk 259584 128 = true := by decide +kernel
private theorem c259712 : checkChunk 259712 128 = true := by decide +kernel
private theorem c259840 : checkChunk 259840 128 = true := by decide +kernel
private theorem c259968 : checkChunk 259968 128 = true := by decide +kernel
private theorem c260096 : checkChunk 260096 128 = true := by decide +kernel
private theorem c260224 : checkChunk 260224 128 = true := by decide +kernel
private theorem c260352 : checkChunk 260352 128 = true := by decide +kernel
private theorem c260480 : checkChunk 260480 128 = true := by decide +kernel
private theorem c260608 : checkChunk 260608 128 = true := by decide +kernel
private theorem c260736 : checkChunk 260736 128 = true := by decide +kernel
private theorem c260864 : checkChunk 260864 128 = true := by decide +kernel
private theorem c260992 : checkChunk 260992 128 = true := by decide +kernel
private theorem c261120 : checkChunk 261120 128 = true := by decide +kernel
private theorem c261248 : checkChunk 261248 128 = true := by decide +kernel
private theorem c261376 : checkChunk 261376 128 = true := by decide +kernel
private theorem c261504 : checkChunk 261504 128 = true := by decide +kernel
private theorem c261632 : checkChunk 261632 128 = true := by decide +kernel
private theorem c261760 : checkChunk 261760 128 = true := by decide +kernel
private theorem c261888 : checkChunk 261888 128 = true := by decide +kernel
private theorem c262016 : checkChunk 262016 128 = true := by decide +kernel

public theorem checked : Checked 253952 262144 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 253952 128 c253952) (checkChunk_sound 254080 128 c254080)) (Checked.append (checkChunk_sound 254208 128 c254208) (checkChunk_sound 254336 128 c254336))) (Checked.append (Checked.append (checkChunk_sound 254464 128 c254464) (checkChunk_sound 254592 128 c254592)) (Checked.append (checkChunk_sound 254720 128 c254720) (checkChunk_sound 254848 128 c254848)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 254976 128 c254976) (checkChunk_sound 255104 128 c255104)) (Checked.append (checkChunk_sound 255232 128 c255232) (checkChunk_sound 255360 128 c255360))) (Checked.append (Checked.append (checkChunk_sound 255488 128 c255488) (checkChunk_sound 255616 128 c255616)) (Checked.append (checkChunk_sound 255744 128 c255744) (checkChunk_sound 255872 128 c255872))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 256000 128 c256000) (checkChunk_sound 256128 128 c256128)) (Checked.append (checkChunk_sound 256256 128 c256256) (checkChunk_sound 256384 128 c256384))) (Checked.append (Checked.append (checkChunk_sound 256512 128 c256512) (checkChunk_sound 256640 128 c256640)) (Checked.append (checkChunk_sound 256768 128 c256768) (checkChunk_sound 256896 128 c256896)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 257024 128 c257024) (checkChunk_sound 257152 128 c257152)) (Checked.append (checkChunk_sound 257280 128 c257280) (checkChunk_sound 257408 128 c257408))) (Checked.append (Checked.append (checkChunk_sound 257536 128 c257536) (checkChunk_sound 257664 128 c257664)) (Checked.append (checkChunk_sound 257792 128 c257792) (checkChunk_sound 257920 128 c257920)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 258048 128 c258048) (checkChunk_sound 258176 128 c258176)) (Checked.append (checkChunk_sound 258304 128 c258304) (checkChunk_sound 258432 128 c258432))) (Checked.append (Checked.append (checkChunk_sound 258560 128 c258560) (checkChunk_sound 258688 128 c258688)) (Checked.append (checkChunk_sound 258816 128 c258816) (checkChunk_sound 258944 128 c258944)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 259072 128 c259072) (checkChunk_sound 259200 128 c259200)) (Checked.append (checkChunk_sound 259328 128 c259328) (checkChunk_sound 259456 128 c259456))) (Checked.append (Checked.append (checkChunk_sound 259584 128 c259584) (checkChunk_sound 259712 128 c259712)) (Checked.append (checkChunk_sound 259840 128 c259840) (checkChunk_sound 259968 128 c259968))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 260096 128 c260096) (checkChunk_sound 260224 128 c260224)) (Checked.append (checkChunk_sound 260352 128 c260352) (checkChunk_sound 260480 128 c260480))) (Checked.append (Checked.append (checkChunk_sound 260608 128 c260608) (checkChunk_sound 260736 128 c260736)) (Checked.append (checkChunk_sound 260864 128 c260864) (checkChunk_sound 260992 128 c260992)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 261120 128 c261120) (checkChunk_sound 261248 128 c261248)) (Checked.append (checkChunk_sound 261376 128 c261376) (checkChunk_sound 261504 128 c261504))) (Checked.append (Checked.append (checkChunk_sound 261632 128 c261632) (checkChunk_sound 261760 128 c261760)) (Checked.append (checkChunk_sound 261888 128 c261888) (checkChunk_sound 262016 128 c262016)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B004
