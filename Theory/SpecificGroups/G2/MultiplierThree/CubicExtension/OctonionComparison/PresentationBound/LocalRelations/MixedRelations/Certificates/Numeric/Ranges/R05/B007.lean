module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1130496, 1138688).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B007
private theorem c1130496 : checkChunk 1130496 128 = true := by decide +kernel
private theorem c1130624 : checkChunk 1130624 128 = true := by decide +kernel
private theorem c1130752 : checkChunk 1130752 128 = true := by decide +kernel
private theorem c1130880 : checkChunk 1130880 128 = true := by decide +kernel
private theorem c1131008 : checkChunk 1131008 128 = true := by decide +kernel
private theorem c1131136 : checkChunk 1131136 128 = true := by decide +kernel
private theorem c1131264 : checkChunk 1131264 128 = true := by decide +kernel
private theorem c1131392 : checkChunk 1131392 128 = true := by decide +kernel
private theorem c1131520 : checkChunk 1131520 128 = true := by decide +kernel
private theorem c1131648 : checkChunk 1131648 128 = true := by decide +kernel
private theorem c1131776 : checkChunk 1131776 128 = true := by decide +kernel
private theorem c1131904 : checkChunk 1131904 128 = true := by decide +kernel
private theorem c1132032 : checkChunk 1132032 128 = true := by decide +kernel
private theorem c1132160 : checkChunk 1132160 128 = true := by decide +kernel
private theorem c1132288 : checkChunk 1132288 128 = true := by decide +kernel
private theorem c1132416 : checkChunk 1132416 128 = true := by decide +kernel
private theorem c1132544 : checkChunk 1132544 128 = true := by decide +kernel
private theorem c1132672 : checkChunk 1132672 128 = true := by decide +kernel
private theorem c1132800 : checkChunk 1132800 128 = true := by decide +kernel
private theorem c1132928 : checkChunk 1132928 128 = true := by decide +kernel
private theorem c1133056 : checkChunk 1133056 128 = true := by decide +kernel
private theorem c1133184 : checkChunk 1133184 128 = true := by decide +kernel
private theorem c1133312 : checkChunk 1133312 128 = true := by decide +kernel
private theorem c1133440 : checkChunk 1133440 128 = true := by decide +kernel
private theorem c1133568 : checkChunk 1133568 128 = true := by decide +kernel
private theorem c1133696 : checkChunk 1133696 128 = true := by decide +kernel
private theorem c1133824 : checkChunk 1133824 128 = true := by decide +kernel
private theorem c1133952 : checkChunk 1133952 128 = true := by decide +kernel
private theorem c1134080 : checkChunk 1134080 128 = true := by decide +kernel
private theorem c1134208 : checkChunk 1134208 128 = true := by decide +kernel
private theorem c1134336 : checkChunk 1134336 128 = true := by decide +kernel
private theorem c1134464 : checkChunk 1134464 128 = true := by decide +kernel
private theorem c1134592 : checkChunk 1134592 128 = true := by decide +kernel
private theorem c1134720 : checkChunk 1134720 128 = true := by decide +kernel
private theorem c1134848 : checkChunk 1134848 128 = true := by decide +kernel
private theorem c1134976 : checkChunk 1134976 128 = true := by decide +kernel
private theorem c1135104 : checkChunk 1135104 128 = true := by decide +kernel
private theorem c1135232 : checkChunk 1135232 128 = true := by decide +kernel
private theorem c1135360 : checkChunk 1135360 128 = true := by decide +kernel
private theorem c1135488 : checkChunk 1135488 128 = true := by decide +kernel
private theorem c1135616 : checkChunk 1135616 128 = true := by decide +kernel
private theorem c1135744 : checkChunk 1135744 128 = true := by decide +kernel
private theorem c1135872 : checkChunk 1135872 128 = true := by decide +kernel
private theorem c1136000 : checkChunk 1136000 128 = true := by decide +kernel
private theorem c1136128 : checkChunk 1136128 128 = true := by decide +kernel
private theorem c1136256 : checkChunk 1136256 128 = true := by decide +kernel
private theorem c1136384 : checkChunk 1136384 128 = true := by decide +kernel
private theorem c1136512 : checkChunk 1136512 128 = true := by decide +kernel
private theorem c1136640 : checkChunk 1136640 128 = true := by decide +kernel
private theorem c1136768 : checkChunk 1136768 128 = true := by decide +kernel
private theorem c1136896 : checkChunk 1136896 128 = true := by decide +kernel
private theorem c1137024 : checkChunk 1137024 128 = true := by decide +kernel
private theorem c1137152 : checkChunk 1137152 128 = true := by decide +kernel
private theorem c1137280 : checkChunk 1137280 128 = true := by decide +kernel
private theorem c1137408 : checkChunk 1137408 128 = true := by decide +kernel
private theorem c1137536 : checkChunk 1137536 128 = true := by decide +kernel
private theorem c1137664 : checkChunk 1137664 128 = true := by decide +kernel
private theorem c1137792 : checkChunk 1137792 128 = true := by decide +kernel
private theorem c1137920 : checkChunk 1137920 128 = true := by decide +kernel
private theorem c1138048 : checkChunk 1138048 128 = true := by decide +kernel
private theorem c1138176 : checkChunk 1138176 128 = true := by decide +kernel
private theorem c1138304 : checkChunk 1138304 128 = true := by decide +kernel
private theorem c1138432 : checkChunk 1138432 128 = true := by decide +kernel
private theorem c1138560 : checkChunk 1138560 128 = true := by decide +kernel

public theorem checked : Checked 1130496 1138688 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1130496 128 c1130496) (checkChunk_sound 1130624 128 c1130624)) (Checked.append (checkChunk_sound 1130752 128 c1130752) (checkChunk_sound 1130880 128 c1130880))) (Checked.append (Checked.append (checkChunk_sound 1131008 128 c1131008) (checkChunk_sound 1131136 128 c1131136)) (Checked.append (checkChunk_sound 1131264 128 c1131264) (checkChunk_sound 1131392 128 c1131392)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1131520 128 c1131520) (checkChunk_sound 1131648 128 c1131648)) (Checked.append (checkChunk_sound 1131776 128 c1131776) (checkChunk_sound 1131904 128 c1131904))) (Checked.append (Checked.append (checkChunk_sound 1132032 128 c1132032) (checkChunk_sound 1132160 128 c1132160)) (Checked.append (checkChunk_sound 1132288 128 c1132288) (checkChunk_sound 1132416 128 c1132416))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1132544 128 c1132544) (checkChunk_sound 1132672 128 c1132672)) (Checked.append (checkChunk_sound 1132800 128 c1132800) (checkChunk_sound 1132928 128 c1132928))) (Checked.append (Checked.append (checkChunk_sound 1133056 128 c1133056) (checkChunk_sound 1133184 128 c1133184)) (Checked.append (checkChunk_sound 1133312 128 c1133312) (checkChunk_sound 1133440 128 c1133440)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1133568 128 c1133568) (checkChunk_sound 1133696 128 c1133696)) (Checked.append (checkChunk_sound 1133824 128 c1133824) (checkChunk_sound 1133952 128 c1133952))) (Checked.append (Checked.append (checkChunk_sound 1134080 128 c1134080) (checkChunk_sound 1134208 128 c1134208)) (Checked.append (checkChunk_sound 1134336 128 c1134336) (checkChunk_sound 1134464 128 c1134464)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1134592 128 c1134592) (checkChunk_sound 1134720 128 c1134720)) (Checked.append (checkChunk_sound 1134848 128 c1134848) (checkChunk_sound 1134976 128 c1134976))) (Checked.append (Checked.append (checkChunk_sound 1135104 128 c1135104) (checkChunk_sound 1135232 128 c1135232)) (Checked.append (checkChunk_sound 1135360 128 c1135360) (checkChunk_sound 1135488 128 c1135488)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1135616 128 c1135616) (checkChunk_sound 1135744 128 c1135744)) (Checked.append (checkChunk_sound 1135872 128 c1135872) (checkChunk_sound 1136000 128 c1136000))) (Checked.append (Checked.append (checkChunk_sound 1136128 128 c1136128) (checkChunk_sound 1136256 128 c1136256)) (Checked.append (checkChunk_sound 1136384 128 c1136384) (checkChunk_sound 1136512 128 c1136512))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1136640 128 c1136640) (checkChunk_sound 1136768 128 c1136768)) (Checked.append (checkChunk_sound 1136896 128 c1136896) (checkChunk_sound 1137024 128 c1137024))) (Checked.append (Checked.append (checkChunk_sound 1137152 128 c1137152) (checkChunk_sound 1137280 128 c1137280)) (Checked.append (checkChunk_sound 1137408 128 c1137408) (checkChunk_sound 1137536 128 c1137536)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1137664 128 c1137664) (checkChunk_sound 1137792 128 c1137792)) (Checked.append (checkChunk_sound 1137920 128 c1137920) (checkChunk_sound 1138048 128 c1138048))) (Checked.append (Checked.append (checkChunk_sound 1138176 128 c1138176) (checkChunk_sound 1138304 128 c1138304)) (Checked.append (checkChunk_sound 1138432 128 c1138432) (checkChunk_sound 1138560 128 c1138560)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B007
