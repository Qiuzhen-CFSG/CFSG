module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1089536, 1097728).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B002
private theorem c1089536 : checkChunk 1089536 128 = true := by decide +kernel
private theorem c1089664 : checkChunk 1089664 128 = true := by decide +kernel
private theorem c1089792 : checkChunk 1089792 128 = true := by decide +kernel
private theorem c1089920 : checkChunk 1089920 128 = true := by decide +kernel
private theorem c1090048 : checkChunk 1090048 128 = true := by decide +kernel
private theorem c1090176 : checkChunk 1090176 128 = true := by decide +kernel
private theorem c1090304 : checkChunk 1090304 128 = true := by decide +kernel
private theorem c1090432 : checkChunk 1090432 128 = true := by decide +kernel
private theorem c1090560 : checkChunk 1090560 128 = true := by decide +kernel
private theorem c1090688 : checkChunk 1090688 128 = true := by decide +kernel
private theorem c1090816 : checkChunk 1090816 128 = true := by decide +kernel
private theorem c1090944 : checkChunk 1090944 128 = true := by decide +kernel
private theorem c1091072 : checkChunk 1091072 128 = true := by decide +kernel
private theorem c1091200 : checkChunk 1091200 128 = true := by decide +kernel
private theorem c1091328 : checkChunk 1091328 128 = true := by decide +kernel
private theorem c1091456 : checkChunk 1091456 128 = true := by decide +kernel
private theorem c1091584 : checkChunk 1091584 128 = true := by decide +kernel
private theorem c1091712 : checkChunk 1091712 128 = true := by decide +kernel
private theorem c1091840 : checkChunk 1091840 128 = true := by decide +kernel
private theorem c1091968 : checkChunk 1091968 128 = true := by decide +kernel
private theorem c1092096 : checkChunk 1092096 128 = true := by decide +kernel
private theorem c1092224 : checkChunk 1092224 128 = true := by decide +kernel
private theorem c1092352 : checkChunk 1092352 128 = true := by decide +kernel
private theorem c1092480 : checkChunk 1092480 128 = true := by decide +kernel
private theorem c1092608 : checkChunk 1092608 128 = true := by decide +kernel
private theorem c1092736 : checkChunk 1092736 128 = true := by decide +kernel
private theorem c1092864 : checkChunk 1092864 128 = true := by decide +kernel
private theorem c1092992 : checkChunk 1092992 128 = true := by decide +kernel
private theorem c1093120 : checkChunk 1093120 128 = true := by decide +kernel
private theorem c1093248 : checkChunk 1093248 128 = true := by decide +kernel
private theorem c1093376 : checkChunk 1093376 128 = true := by decide +kernel
private theorem c1093504 : checkChunk 1093504 128 = true := by decide +kernel
private theorem c1093632 : checkChunk 1093632 128 = true := by decide +kernel
private theorem c1093760 : checkChunk 1093760 128 = true := by decide +kernel
private theorem c1093888 : checkChunk 1093888 128 = true := by decide +kernel
private theorem c1094016 : checkChunk 1094016 128 = true := by decide +kernel
private theorem c1094144 : checkChunk 1094144 128 = true := by decide +kernel
private theorem c1094272 : checkChunk 1094272 128 = true := by decide +kernel
private theorem c1094400 : checkChunk 1094400 128 = true := by decide +kernel
private theorem c1094528 : checkChunk 1094528 128 = true := by decide +kernel
private theorem c1094656 : checkChunk 1094656 128 = true := by decide +kernel
private theorem c1094784 : checkChunk 1094784 128 = true := by decide +kernel
private theorem c1094912 : checkChunk 1094912 128 = true := by decide +kernel
private theorem c1095040 : checkChunk 1095040 128 = true := by decide +kernel
private theorem c1095168 : checkChunk 1095168 128 = true := by decide +kernel
private theorem c1095296 : checkChunk 1095296 128 = true := by decide +kernel
private theorem c1095424 : checkChunk 1095424 128 = true := by decide +kernel
private theorem c1095552 : checkChunk 1095552 128 = true := by decide +kernel
private theorem c1095680 : checkChunk 1095680 128 = true := by decide +kernel
private theorem c1095808 : checkChunk 1095808 128 = true := by decide +kernel
private theorem c1095936 : checkChunk 1095936 128 = true := by decide +kernel
private theorem c1096064 : checkChunk 1096064 128 = true := by decide +kernel
private theorem c1096192 : checkChunk 1096192 128 = true := by decide +kernel
private theorem c1096320 : checkChunk 1096320 128 = true := by decide +kernel
private theorem c1096448 : checkChunk 1096448 128 = true := by decide +kernel
private theorem c1096576 : checkChunk 1096576 128 = true := by decide +kernel
private theorem c1096704 : checkChunk 1096704 128 = true := by decide +kernel
private theorem c1096832 : checkChunk 1096832 128 = true := by decide +kernel
private theorem c1096960 : checkChunk 1096960 128 = true := by decide +kernel
private theorem c1097088 : checkChunk 1097088 128 = true := by decide +kernel
private theorem c1097216 : checkChunk 1097216 128 = true := by decide +kernel
private theorem c1097344 : checkChunk 1097344 128 = true := by decide +kernel
private theorem c1097472 : checkChunk 1097472 128 = true := by decide +kernel
private theorem c1097600 : checkChunk 1097600 128 = true := by decide +kernel

public theorem checked : Checked 1089536 1097728 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1089536 128 c1089536) (checkChunk_sound 1089664 128 c1089664)) (Checked.append (checkChunk_sound 1089792 128 c1089792) (checkChunk_sound 1089920 128 c1089920))) (Checked.append (Checked.append (checkChunk_sound 1090048 128 c1090048) (checkChunk_sound 1090176 128 c1090176)) (Checked.append (checkChunk_sound 1090304 128 c1090304) (checkChunk_sound 1090432 128 c1090432)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1090560 128 c1090560) (checkChunk_sound 1090688 128 c1090688)) (Checked.append (checkChunk_sound 1090816 128 c1090816) (checkChunk_sound 1090944 128 c1090944))) (Checked.append (Checked.append (checkChunk_sound 1091072 128 c1091072) (checkChunk_sound 1091200 128 c1091200)) (Checked.append (checkChunk_sound 1091328 128 c1091328) (checkChunk_sound 1091456 128 c1091456))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1091584 128 c1091584) (checkChunk_sound 1091712 128 c1091712)) (Checked.append (checkChunk_sound 1091840 128 c1091840) (checkChunk_sound 1091968 128 c1091968))) (Checked.append (Checked.append (checkChunk_sound 1092096 128 c1092096) (checkChunk_sound 1092224 128 c1092224)) (Checked.append (checkChunk_sound 1092352 128 c1092352) (checkChunk_sound 1092480 128 c1092480)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1092608 128 c1092608) (checkChunk_sound 1092736 128 c1092736)) (Checked.append (checkChunk_sound 1092864 128 c1092864) (checkChunk_sound 1092992 128 c1092992))) (Checked.append (Checked.append (checkChunk_sound 1093120 128 c1093120) (checkChunk_sound 1093248 128 c1093248)) (Checked.append (checkChunk_sound 1093376 128 c1093376) (checkChunk_sound 1093504 128 c1093504)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1093632 128 c1093632) (checkChunk_sound 1093760 128 c1093760)) (Checked.append (checkChunk_sound 1093888 128 c1093888) (checkChunk_sound 1094016 128 c1094016))) (Checked.append (Checked.append (checkChunk_sound 1094144 128 c1094144) (checkChunk_sound 1094272 128 c1094272)) (Checked.append (checkChunk_sound 1094400 128 c1094400) (checkChunk_sound 1094528 128 c1094528)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1094656 128 c1094656) (checkChunk_sound 1094784 128 c1094784)) (Checked.append (checkChunk_sound 1094912 128 c1094912) (checkChunk_sound 1095040 128 c1095040))) (Checked.append (Checked.append (checkChunk_sound 1095168 128 c1095168) (checkChunk_sound 1095296 128 c1095296)) (Checked.append (checkChunk_sound 1095424 128 c1095424) (checkChunk_sound 1095552 128 c1095552))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1095680 128 c1095680) (checkChunk_sound 1095808 128 c1095808)) (Checked.append (checkChunk_sound 1095936 128 c1095936) (checkChunk_sound 1096064 128 c1096064))) (Checked.append (Checked.append (checkChunk_sound 1096192 128 c1096192) (checkChunk_sound 1096320 128 c1096320)) (Checked.append (checkChunk_sound 1096448 128 c1096448) (checkChunk_sound 1096576 128 c1096576)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1096704 128 c1096704) (checkChunk_sound 1096832 128 c1096832)) (Checked.append (checkChunk_sound 1096960 128 c1096960) (checkChunk_sound 1097088 128 c1097088))) (Checked.append (Checked.append (checkChunk_sound 1097216 128 c1097216) (checkChunk_sound 1097344 128 c1097344)) (Checked.append (checkChunk_sound 1097472 128 c1097472) (checkChunk_sound 1097600 128 c1097600)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B002
