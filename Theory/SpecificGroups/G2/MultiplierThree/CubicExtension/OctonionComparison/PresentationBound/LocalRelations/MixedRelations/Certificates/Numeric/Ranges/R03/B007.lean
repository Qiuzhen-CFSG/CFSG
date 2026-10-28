module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [704512, 712704).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B007
private theorem c704512 : checkChunk 704512 128 = true := by decide +kernel
private theorem c704640 : checkChunk 704640 128 = true := by decide +kernel
private theorem c704768 : checkChunk 704768 128 = true := by decide +kernel
private theorem c704896 : checkChunk 704896 128 = true := by decide +kernel
private theorem c705024 : checkChunk 705024 128 = true := by decide +kernel
private theorem c705152 : checkChunk 705152 128 = true := by decide +kernel
private theorem c705280 : checkChunk 705280 128 = true := by decide +kernel
private theorem c705408 : checkChunk 705408 128 = true := by decide +kernel
private theorem c705536 : checkChunk 705536 128 = true := by decide +kernel
private theorem c705664 : checkChunk 705664 128 = true := by decide +kernel
private theorem c705792 : checkChunk 705792 128 = true := by decide +kernel
private theorem c705920 : checkChunk 705920 128 = true := by decide +kernel
private theorem c706048 : checkChunk 706048 128 = true := by decide +kernel
private theorem c706176 : checkChunk 706176 128 = true := by decide +kernel
private theorem c706304 : checkChunk 706304 128 = true := by decide +kernel
private theorem c706432 : checkChunk 706432 128 = true := by decide +kernel
private theorem c706560 : checkChunk 706560 128 = true := by decide +kernel
private theorem c706688 : checkChunk 706688 128 = true := by decide +kernel
private theorem c706816 : checkChunk 706816 128 = true := by decide +kernel
private theorem c706944 : checkChunk 706944 128 = true := by decide +kernel
private theorem c707072 : checkChunk 707072 128 = true := by decide +kernel
private theorem c707200 : checkChunk 707200 128 = true := by decide +kernel
private theorem c707328 : checkChunk 707328 128 = true := by decide +kernel
private theorem c707456 : checkChunk 707456 128 = true := by decide +kernel
private theorem c707584 : checkChunk 707584 128 = true := by decide +kernel
private theorem c707712 : checkChunk 707712 128 = true := by decide +kernel
private theorem c707840 : checkChunk 707840 128 = true := by decide +kernel
private theorem c707968 : checkChunk 707968 128 = true := by decide +kernel
private theorem c708096 : checkChunk 708096 128 = true := by decide +kernel
private theorem c708224 : checkChunk 708224 128 = true := by decide +kernel
private theorem c708352 : checkChunk 708352 128 = true := by decide +kernel
private theorem c708480 : checkChunk 708480 128 = true := by decide +kernel
private theorem c708608 : checkChunk 708608 128 = true := by decide +kernel
private theorem c708736 : checkChunk 708736 128 = true := by decide +kernel
private theorem c708864 : checkChunk 708864 128 = true := by decide +kernel
private theorem c708992 : checkChunk 708992 128 = true := by decide +kernel
private theorem c709120 : checkChunk 709120 128 = true := by decide +kernel
private theorem c709248 : checkChunk 709248 128 = true := by decide +kernel
private theorem c709376 : checkChunk 709376 128 = true := by decide +kernel
private theorem c709504 : checkChunk 709504 128 = true := by decide +kernel
private theorem c709632 : checkChunk 709632 128 = true := by decide +kernel
private theorem c709760 : checkChunk 709760 128 = true := by decide +kernel
private theorem c709888 : checkChunk 709888 128 = true := by decide +kernel
private theorem c710016 : checkChunk 710016 128 = true := by decide +kernel
private theorem c710144 : checkChunk 710144 128 = true := by decide +kernel
private theorem c710272 : checkChunk 710272 128 = true := by decide +kernel
private theorem c710400 : checkChunk 710400 128 = true := by decide +kernel
private theorem c710528 : checkChunk 710528 128 = true := by decide +kernel
private theorem c710656 : checkChunk 710656 128 = true := by decide +kernel
private theorem c710784 : checkChunk 710784 128 = true := by decide +kernel
private theorem c710912 : checkChunk 710912 128 = true := by decide +kernel
private theorem c711040 : checkChunk 711040 128 = true := by decide +kernel
private theorem c711168 : checkChunk 711168 128 = true := by decide +kernel
private theorem c711296 : checkChunk 711296 128 = true := by decide +kernel
private theorem c711424 : checkChunk 711424 128 = true := by decide +kernel
private theorem c711552 : checkChunk 711552 128 = true := by decide +kernel
private theorem c711680 : checkChunk 711680 128 = true := by decide +kernel
private theorem c711808 : checkChunk 711808 128 = true := by decide +kernel
private theorem c711936 : checkChunk 711936 128 = true := by decide +kernel
private theorem c712064 : checkChunk 712064 128 = true := by decide +kernel
private theorem c712192 : checkChunk 712192 128 = true := by decide +kernel
private theorem c712320 : checkChunk 712320 128 = true := by decide +kernel
private theorem c712448 : checkChunk 712448 128 = true := by decide +kernel
private theorem c712576 : checkChunk 712576 128 = true := by decide +kernel

public theorem checked : Checked 704512 712704 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 704512 128 c704512) (checkChunk_sound 704640 128 c704640)) (Checked.append (checkChunk_sound 704768 128 c704768) (checkChunk_sound 704896 128 c704896))) (Checked.append (Checked.append (checkChunk_sound 705024 128 c705024) (checkChunk_sound 705152 128 c705152)) (Checked.append (checkChunk_sound 705280 128 c705280) (checkChunk_sound 705408 128 c705408)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 705536 128 c705536) (checkChunk_sound 705664 128 c705664)) (Checked.append (checkChunk_sound 705792 128 c705792) (checkChunk_sound 705920 128 c705920))) (Checked.append (Checked.append (checkChunk_sound 706048 128 c706048) (checkChunk_sound 706176 128 c706176)) (Checked.append (checkChunk_sound 706304 128 c706304) (checkChunk_sound 706432 128 c706432))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 706560 128 c706560) (checkChunk_sound 706688 128 c706688)) (Checked.append (checkChunk_sound 706816 128 c706816) (checkChunk_sound 706944 128 c706944))) (Checked.append (Checked.append (checkChunk_sound 707072 128 c707072) (checkChunk_sound 707200 128 c707200)) (Checked.append (checkChunk_sound 707328 128 c707328) (checkChunk_sound 707456 128 c707456)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 707584 128 c707584) (checkChunk_sound 707712 128 c707712)) (Checked.append (checkChunk_sound 707840 128 c707840) (checkChunk_sound 707968 128 c707968))) (Checked.append (Checked.append (checkChunk_sound 708096 128 c708096) (checkChunk_sound 708224 128 c708224)) (Checked.append (checkChunk_sound 708352 128 c708352) (checkChunk_sound 708480 128 c708480)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 708608 128 c708608) (checkChunk_sound 708736 128 c708736)) (Checked.append (checkChunk_sound 708864 128 c708864) (checkChunk_sound 708992 128 c708992))) (Checked.append (Checked.append (checkChunk_sound 709120 128 c709120) (checkChunk_sound 709248 128 c709248)) (Checked.append (checkChunk_sound 709376 128 c709376) (checkChunk_sound 709504 128 c709504)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 709632 128 c709632) (checkChunk_sound 709760 128 c709760)) (Checked.append (checkChunk_sound 709888 128 c709888) (checkChunk_sound 710016 128 c710016))) (Checked.append (Checked.append (checkChunk_sound 710144 128 c710144) (checkChunk_sound 710272 128 c710272)) (Checked.append (checkChunk_sound 710400 128 c710400) (checkChunk_sound 710528 128 c710528))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 710656 128 c710656) (checkChunk_sound 710784 128 c710784)) (Checked.append (checkChunk_sound 710912 128 c710912) (checkChunk_sound 711040 128 c711040))) (Checked.append (Checked.append (checkChunk_sound 711168 128 c711168) (checkChunk_sound 711296 128 c711296)) (Checked.append (checkChunk_sound 711424 128 c711424) (checkChunk_sound 711552 128 c711552)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 711680 128 c711680) (checkChunk_sound 711808 128 c711808)) (Checked.append (checkChunk_sound 711936 128 c711936) (checkChunk_sound 712064 128 c712064))) (Checked.append (Checked.append (checkChunk_sound 712192 128 c712192) (checkChunk_sound 712320 128 c712320)) (Checked.append (checkChunk_sound 712448 128 c712448) (checkChunk_sound 712576 128 c712576)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B007
