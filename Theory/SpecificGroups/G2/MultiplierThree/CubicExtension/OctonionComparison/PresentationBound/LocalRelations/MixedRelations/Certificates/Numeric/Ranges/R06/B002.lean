module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1302528, 1310720).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B002
private theorem c1302528 : checkChunk 1302528 128 = true := by decide +kernel
private theorem c1302656 : checkChunk 1302656 128 = true := by decide +kernel
private theorem c1302784 : checkChunk 1302784 128 = true := by decide +kernel
private theorem c1302912 : checkChunk 1302912 128 = true := by decide +kernel
private theorem c1303040 : checkChunk 1303040 128 = true := by decide +kernel
private theorem c1303168 : checkChunk 1303168 128 = true := by decide +kernel
private theorem c1303296 : checkChunk 1303296 128 = true := by decide +kernel
private theorem c1303424 : checkChunk 1303424 128 = true := by decide +kernel
private theorem c1303552 : checkChunk 1303552 128 = true := by decide +kernel
private theorem c1303680 : checkChunk 1303680 128 = true := by decide +kernel
private theorem c1303808 : checkChunk 1303808 128 = true := by decide +kernel
private theorem c1303936 : checkChunk 1303936 128 = true := by decide +kernel
private theorem c1304064 : checkChunk 1304064 128 = true := by decide +kernel
private theorem c1304192 : checkChunk 1304192 128 = true := by decide +kernel
private theorem c1304320 : checkChunk 1304320 128 = true := by decide +kernel
private theorem c1304448 : checkChunk 1304448 128 = true := by decide +kernel
private theorem c1304576 : checkChunk 1304576 128 = true := by decide +kernel
private theorem c1304704 : checkChunk 1304704 128 = true := by decide +kernel
private theorem c1304832 : checkChunk 1304832 128 = true := by decide +kernel
private theorem c1304960 : checkChunk 1304960 128 = true := by decide +kernel
private theorem c1305088 : checkChunk 1305088 128 = true := by decide +kernel
private theorem c1305216 : checkChunk 1305216 128 = true := by decide +kernel
private theorem c1305344 : checkChunk 1305344 128 = true := by decide +kernel
private theorem c1305472 : checkChunk 1305472 128 = true := by decide +kernel
private theorem c1305600 : checkChunk 1305600 128 = true := by decide +kernel
private theorem c1305728 : checkChunk 1305728 128 = true := by decide +kernel
private theorem c1305856 : checkChunk 1305856 128 = true := by decide +kernel
private theorem c1305984 : checkChunk 1305984 128 = true := by decide +kernel
private theorem c1306112 : checkChunk 1306112 128 = true := by decide +kernel
private theorem c1306240 : checkChunk 1306240 128 = true := by decide +kernel
private theorem c1306368 : checkChunk 1306368 128 = true := by decide +kernel
private theorem c1306496 : checkChunk 1306496 128 = true := by decide +kernel
private theorem c1306624 : checkChunk 1306624 128 = true := by decide +kernel
private theorem c1306752 : checkChunk 1306752 128 = true := by decide +kernel
private theorem c1306880 : checkChunk 1306880 128 = true := by decide +kernel
private theorem c1307008 : checkChunk 1307008 128 = true := by decide +kernel
private theorem c1307136 : checkChunk 1307136 128 = true := by decide +kernel
private theorem c1307264 : checkChunk 1307264 128 = true := by decide +kernel
private theorem c1307392 : checkChunk 1307392 128 = true := by decide +kernel
private theorem c1307520 : checkChunk 1307520 128 = true := by decide +kernel
private theorem c1307648 : checkChunk 1307648 128 = true := by decide +kernel
private theorem c1307776 : checkChunk 1307776 128 = true := by decide +kernel
private theorem c1307904 : checkChunk 1307904 128 = true := by decide +kernel
private theorem c1308032 : checkChunk 1308032 128 = true := by decide +kernel
private theorem c1308160 : checkChunk 1308160 128 = true := by decide +kernel
private theorem c1308288 : checkChunk 1308288 128 = true := by decide +kernel
private theorem c1308416 : checkChunk 1308416 128 = true := by decide +kernel
private theorem c1308544 : checkChunk 1308544 128 = true := by decide +kernel
private theorem c1308672 : checkChunk 1308672 128 = true := by decide +kernel
private theorem c1308800 : checkChunk 1308800 128 = true := by decide +kernel
private theorem c1308928 : checkChunk 1308928 128 = true := by decide +kernel
private theorem c1309056 : checkChunk 1309056 128 = true := by decide +kernel
private theorem c1309184 : checkChunk 1309184 128 = true := by decide +kernel
private theorem c1309312 : checkChunk 1309312 128 = true := by decide +kernel
private theorem c1309440 : checkChunk 1309440 128 = true := by decide +kernel
private theorem c1309568 : checkChunk 1309568 128 = true := by decide +kernel
private theorem c1309696 : checkChunk 1309696 128 = true := by decide +kernel
private theorem c1309824 : checkChunk 1309824 128 = true := by decide +kernel
private theorem c1309952 : checkChunk 1309952 128 = true := by decide +kernel
private theorem c1310080 : checkChunk 1310080 128 = true := by decide +kernel
private theorem c1310208 : checkChunk 1310208 128 = true := by decide +kernel
private theorem c1310336 : checkChunk 1310336 128 = true := by decide +kernel
private theorem c1310464 : checkChunk 1310464 128 = true := by decide +kernel
private theorem c1310592 : checkChunk 1310592 128 = true := by decide +kernel

public theorem checked : Checked 1302528 1310720 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1302528 128 c1302528) (checkChunk_sound 1302656 128 c1302656)) (Checked.append (checkChunk_sound 1302784 128 c1302784) (checkChunk_sound 1302912 128 c1302912))) (Checked.append (Checked.append (checkChunk_sound 1303040 128 c1303040) (checkChunk_sound 1303168 128 c1303168)) (Checked.append (checkChunk_sound 1303296 128 c1303296) (checkChunk_sound 1303424 128 c1303424)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1303552 128 c1303552) (checkChunk_sound 1303680 128 c1303680)) (Checked.append (checkChunk_sound 1303808 128 c1303808) (checkChunk_sound 1303936 128 c1303936))) (Checked.append (Checked.append (checkChunk_sound 1304064 128 c1304064) (checkChunk_sound 1304192 128 c1304192)) (Checked.append (checkChunk_sound 1304320 128 c1304320) (checkChunk_sound 1304448 128 c1304448))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1304576 128 c1304576) (checkChunk_sound 1304704 128 c1304704)) (Checked.append (checkChunk_sound 1304832 128 c1304832) (checkChunk_sound 1304960 128 c1304960))) (Checked.append (Checked.append (checkChunk_sound 1305088 128 c1305088) (checkChunk_sound 1305216 128 c1305216)) (Checked.append (checkChunk_sound 1305344 128 c1305344) (checkChunk_sound 1305472 128 c1305472)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1305600 128 c1305600) (checkChunk_sound 1305728 128 c1305728)) (Checked.append (checkChunk_sound 1305856 128 c1305856) (checkChunk_sound 1305984 128 c1305984))) (Checked.append (Checked.append (checkChunk_sound 1306112 128 c1306112) (checkChunk_sound 1306240 128 c1306240)) (Checked.append (checkChunk_sound 1306368 128 c1306368) (checkChunk_sound 1306496 128 c1306496)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1306624 128 c1306624) (checkChunk_sound 1306752 128 c1306752)) (Checked.append (checkChunk_sound 1306880 128 c1306880) (checkChunk_sound 1307008 128 c1307008))) (Checked.append (Checked.append (checkChunk_sound 1307136 128 c1307136) (checkChunk_sound 1307264 128 c1307264)) (Checked.append (checkChunk_sound 1307392 128 c1307392) (checkChunk_sound 1307520 128 c1307520)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1307648 128 c1307648) (checkChunk_sound 1307776 128 c1307776)) (Checked.append (checkChunk_sound 1307904 128 c1307904) (checkChunk_sound 1308032 128 c1308032))) (Checked.append (Checked.append (checkChunk_sound 1308160 128 c1308160) (checkChunk_sound 1308288 128 c1308288)) (Checked.append (checkChunk_sound 1308416 128 c1308416) (checkChunk_sound 1308544 128 c1308544))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1308672 128 c1308672) (checkChunk_sound 1308800 128 c1308800)) (Checked.append (checkChunk_sound 1308928 128 c1308928) (checkChunk_sound 1309056 128 c1309056))) (Checked.append (Checked.append (checkChunk_sound 1309184 128 c1309184) (checkChunk_sound 1309312 128 c1309312)) (Checked.append (checkChunk_sound 1309440 128 c1309440) (checkChunk_sound 1309568 128 c1309568)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1309696 128 c1309696) (checkChunk_sound 1309824 128 c1309824)) (Checked.append (checkChunk_sound 1309952 128 c1309952) (checkChunk_sound 1310080 128 c1310080))) (Checked.append (Checked.append (checkChunk_sound 1310208 128 c1310208) (checkChunk_sound 1310336 128 c1310336)) (Checked.append (checkChunk_sound 1310464 128 c1310464) (checkChunk_sound 1310592 128 c1310592)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B002
