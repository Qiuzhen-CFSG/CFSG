module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1212416, 1220608).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B017
private theorem c1212416 : checkChunk 1212416 128 = true := by decide +kernel
private theorem c1212544 : checkChunk 1212544 128 = true := by decide +kernel
private theorem c1212672 : checkChunk 1212672 128 = true := by decide +kernel
private theorem c1212800 : checkChunk 1212800 128 = true := by decide +kernel
private theorem c1212928 : checkChunk 1212928 128 = true := by decide +kernel
private theorem c1213056 : checkChunk 1213056 128 = true := by decide +kernel
private theorem c1213184 : checkChunk 1213184 128 = true := by decide +kernel
private theorem c1213312 : checkChunk 1213312 128 = true := by decide +kernel
private theorem c1213440 : checkChunk 1213440 128 = true := by decide +kernel
private theorem c1213568 : checkChunk 1213568 128 = true := by decide +kernel
private theorem c1213696 : checkChunk 1213696 128 = true := by decide +kernel
private theorem c1213824 : checkChunk 1213824 128 = true := by decide +kernel
private theorem c1213952 : checkChunk 1213952 128 = true := by decide +kernel
private theorem c1214080 : checkChunk 1214080 128 = true := by decide +kernel
private theorem c1214208 : checkChunk 1214208 128 = true := by decide +kernel
private theorem c1214336 : checkChunk 1214336 128 = true := by decide +kernel
private theorem c1214464 : checkChunk 1214464 128 = true := by decide +kernel
private theorem c1214592 : checkChunk 1214592 128 = true := by decide +kernel
private theorem c1214720 : checkChunk 1214720 128 = true := by decide +kernel
private theorem c1214848 : checkChunk 1214848 128 = true := by decide +kernel
private theorem c1214976 : checkChunk 1214976 128 = true := by decide +kernel
private theorem c1215104 : checkChunk 1215104 128 = true := by decide +kernel
private theorem c1215232 : checkChunk 1215232 128 = true := by decide +kernel
private theorem c1215360 : checkChunk 1215360 128 = true := by decide +kernel
private theorem c1215488 : checkChunk 1215488 128 = true := by decide +kernel
private theorem c1215616 : checkChunk 1215616 128 = true := by decide +kernel
private theorem c1215744 : checkChunk 1215744 128 = true := by decide +kernel
private theorem c1215872 : checkChunk 1215872 128 = true := by decide +kernel
private theorem c1216000 : checkChunk 1216000 128 = true := by decide +kernel
private theorem c1216128 : checkChunk 1216128 128 = true := by decide +kernel
private theorem c1216256 : checkChunk 1216256 128 = true := by decide +kernel
private theorem c1216384 : checkChunk 1216384 128 = true := by decide +kernel
private theorem c1216512 : checkChunk 1216512 128 = true := by decide +kernel
private theorem c1216640 : checkChunk 1216640 128 = true := by decide +kernel
private theorem c1216768 : checkChunk 1216768 128 = true := by decide +kernel
private theorem c1216896 : checkChunk 1216896 128 = true := by decide +kernel
private theorem c1217024 : checkChunk 1217024 128 = true := by decide +kernel
private theorem c1217152 : checkChunk 1217152 128 = true := by decide +kernel
private theorem c1217280 : checkChunk 1217280 128 = true := by decide +kernel
private theorem c1217408 : checkChunk 1217408 128 = true := by decide +kernel
private theorem c1217536 : checkChunk 1217536 128 = true := by decide +kernel
private theorem c1217664 : checkChunk 1217664 128 = true := by decide +kernel
private theorem c1217792 : checkChunk 1217792 128 = true := by decide +kernel
private theorem c1217920 : checkChunk 1217920 128 = true := by decide +kernel
private theorem c1218048 : checkChunk 1218048 128 = true := by decide +kernel
private theorem c1218176 : checkChunk 1218176 128 = true := by decide +kernel
private theorem c1218304 : checkChunk 1218304 128 = true := by decide +kernel
private theorem c1218432 : checkChunk 1218432 128 = true := by decide +kernel
private theorem c1218560 : checkChunk 1218560 128 = true := by decide +kernel
private theorem c1218688 : checkChunk 1218688 128 = true := by decide +kernel
private theorem c1218816 : checkChunk 1218816 128 = true := by decide +kernel
private theorem c1218944 : checkChunk 1218944 128 = true := by decide +kernel
private theorem c1219072 : checkChunk 1219072 128 = true := by decide +kernel
private theorem c1219200 : checkChunk 1219200 128 = true := by decide +kernel
private theorem c1219328 : checkChunk 1219328 128 = true := by decide +kernel
private theorem c1219456 : checkChunk 1219456 128 = true := by decide +kernel
private theorem c1219584 : checkChunk 1219584 128 = true := by decide +kernel
private theorem c1219712 : checkChunk 1219712 128 = true := by decide +kernel
private theorem c1219840 : checkChunk 1219840 128 = true := by decide +kernel
private theorem c1219968 : checkChunk 1219968 128 = true := by decide +kernel
private theorem c1220096 : checkChunk 1220096 128 = true := by decide +kernel
private theorem c1220224 : checkChunk 1220224 128 = true := by decide +kernel
private theorem c1220352 : checkChunk 1220352 128 = true := by decide +kernel
private theorem c1220480 : checkChunk 1220480 128 = true := by decide +kernel

public theorem checked : Checked 1212416 1220608 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1212416 128 c1212416) (checkChunk_sound 1212544 128 c1212544)) (Checked.append (checkChunk_sound 1212672 128 c1212672) (checkChunk_sound 1212800 128 c1212800))) (Checked.append (Checked.append (checkChunk_sound 1212928 128 c1212928) (checkChunk_sound 1213056 128 c1213056)) (Checked.append (checkChunk_sound 1213184 128 c1213184) (checkChunk_sound 1213312 128 c1213312)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1213440 128 c1213440) (checkChunk_sound 1213568 128 c1213568)) (Checked.append (checkChunk_sound 1213696 128 c1213696) (checkChunk_sound 1213824 128 c1213824))) (Checked.append (Checked.append (checkChunk_sound 1213952 128 c1213952) (checkChunk_sound 1214080 128 c1214080)) (Checked.append (checkChunk_sound 1214208 128 c1214208) (checkChunk_sound 1214336 128 c1214336))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1214464 128 c1214464) (checkChunk_sound 1214592 128 c1214592)) (Checked.append (checkChunk_sound 1214720 128 c1214720) (checkChunk_sound 1214848 128 c1214848))) (Checked.append (Checked.append (checkChunk_sound 1214976 128 c1214976) (checkChunk_sound 1215104 128 c1215104)) (Checked.append (checkChunk_sound 1215232 128 c1215232) (checkChunk_sound 1215360 128 c1215360)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1215488 128 c1215488) (checkChunk_sound 1215616 128 c1215616)) (Checked.append (checkChunk_sound 1215744 128 c1215744) (checkChunk_sound 1215872 128 c1215872))) (Checked.append (Checked.append (checkChunk_sound 1216000 128 c1216000) (checkChunk_sound 1216128 128 c1216128)) (Checked.append (checkChunk_sound 1216256 128 c1216256) (checkChunk_sound 1216384 128 c1216384)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1216512 128 c1216512) (checkChunk_sound 1216640 128 c1216640)) (Checked.append (checkChunk_sound 1216768 128 c1216768) (checkChunk_sound 1216896 128 c1216896))) (Checked.append (Checked.append (checkChunk_sound 1217024 128 c1217024) (checkChunk_sound 1217152 128 c1217152)) (Checked.append (checkChunk_sound 1217280 128 c1217280) (checkChunk_sound 1217408 128 c1217408)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1217536 128 c1217536) (checkChunk_sound 1217664 128 c1217664)) (Checked.append (checkChunk_sound 1217792 128 c1217792) (checkChunk_sound 1217920 128 c1217920))) (Checked.append (Checked.append (checkChunk_sound 1218048 128 c1218048) (checkChunk_sound 1218176 128 c1218176)) (Checked.append (checkChunk_sound 1218304 128 c1218304) (checkChunk_sound 1218432 128 c1218432))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1218560 128 c1218560) (checkChunk_sound 1218688 128 c1218688)) (Checked.append (checkChunk_sound 1218816 128 c1218816) (checkChunk_sound 1218944 128 c1218944))) (Checked.append (Checked.append (checkChunk_sound 1219072 128 c1219072) (checkChunk_sound 1219200 128 c1219200)) (Checked.append (checkChunk_sound 1219328 128 c1219328) (checkChunk_sound 1219456 128 c1219456)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1219584 128 c1219584) (checkChunk_sound 1219712 128 c1219712)) (Checked.append (checkChunk_sound 1219840 128 c1219840) (checkChunk_sound 1219968 128 c1219968))) (Checked.append (Checked.append (checkChunk_sound 1220096 128 c1220096) (checkChunk_sound 1220224 128 c1220224)) (Checked.append (checkChunk_sound 1220352 128 c1220352) (checkChunk_sound 1220480 128 c1220480)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B017
