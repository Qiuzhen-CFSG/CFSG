module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1409024, 1417216).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B015
private theorem c1409024 : checkChunk 1409024 128 = true := by decide +kernel
private theorem c1409152 : checkChunk 1409152 128 = true := by decide +kernel
private theorem c1409280 : checkChunk 1409280 128 = true := by decide +kernel
private theorem c1409408 : checkChunk 1409408 128 = true := by decide +kernel
private theorem c1409536 : checkChunk 1409536 128 = true := by decide +kernel
private theorem c1409664 : checkChunk 1409664 128 = true := by decide +kernel
private theorem c1409792 : checkChunk 1409792 128 = true := by decide +kernel
private theorem c1409920 : checkChunk 1409920 128 = true := by decide +kernel
private theorem c1410048 : checkChunk 1410048 128 = true := by decide +kernel
private theorem c1410176 : checkChunk 1410176 128 = true := by decide +kernel
private theorem c1410304 : checkChunk 1410304 128 = true := by decide +kernel
private theorem c1410432 : checkChunk 1410432 128 = true := by decide +kernel
private theorem c1410560 : checkChunk 1410560 128 = true := by decide +kernel
private theorem c1410688 : checkChunk 1410688 128 = true := by decide +kernel
private theorem c1410816 : checkChunk 1410816 128 = true := by decide +kernel
private theorem c1410944 : checkChunk 1410944 128 = true := by decide +kernel
private theorem c1411072 : checkChunk 1411072 128 = true := by decide +kernel
private theorem c1411200 : checkChunk 1411200 128 = true := by decide +kernel
private theorem c1411328 : checkChunk 1411328 128 = true := by decide +kernel
private theorem c1411456 : checkChunk 1411456 128 = true := by decide +kernel
private theorem c1411584 : checkChunk 1411584 128 = true := by decide +kernel
private theorem c1411712 : checkChunk 1411712 128 = true := by decide +kernel
private theorem c1411840 : checkChunk 1411840 128 = true := by decide +kernel
private theorem c1411968 : checkChunk 1411968 128 = true := by decide +kernel
private theorem c1412096 : checkChunk 1412096 128 = true := by decide +kernel
private theorem c1412224 : checkChunk 1412224 128 = true := by decide +kernel
private theorem c1412352 : checkChunk 1412352 128 = true := by decide +kernel
private theorem c1412480 : checkChunk 1412480 128 = true := by decide +kernel
private theorem c1412608 : checkChunk 1412608 128 = true := by decide +kernel
private theorem c1412736 : checkChunk 1412736 128 = true := by decide +kernel
private theorem c1412864 : checkChunk 1412864 128 = true := by decide +kernel
private theorem c1412992 : checkChunk 1412992 128 = true := by decide +kernel
private theorem c1413120 : checkChunk 1413120 128 = true := by decide +kernel
private theorem c1413248 : checkChunk 1413248 128 = true := by decide +kernel
private theorem c1413376 : checkChunk 1413376 128 = true := by decide +kernel
private theorem c1413504 : checkChunk 1413504 128 = true := by decide +kernel
private theorem c1413632 : checkChunk 1413632 128 = true := by decide +kernel
private theorem c1413760 : checkChunk 1413760 128 = true := by decide +kernel
private theorem c1413888 : checkChunk 1413888 128 = true := by decide +kernel
private theorem c1414016 : checkChunk 1414016 128 = true := by decide +kernel
private theorem c1414144 : checkChunk 1414144 128 = true := by decide +kernel
private theorem c1414272 : checkChunk 1414272 128 = true := by decide +kernel
private theorem c1414400 : checkChunk 1414400 128 = true := by decide +kernel
private theorem c1414528 : checkChunk 1414528 128 = true := by decide +kernel
private theorem c1414656 : checkChunk 1414656 128 = true := by decide +kernel
private theorem c1414784 : checkChunk 1414784 128 = true := by decide +kernel
private theorem c1414912 : checkChunk 1414912 128 = true := by decide +kernel
private theorem c1415040 : checkChunk 1415040 128 = true := by decide +kernel
private theorem c1415168 : checkChunk 1415168 128 = true := by decide +kernel
private theorem c1415296 : checkChunk 1415296 128 = true := by decide +kernel
private theorem c1415424 : checkChunk 1415424 128 = true := by decide +kernel
private theorem c1415552 : checkChunk 1415552 128 = true := by decide +kernel
private theorem c1415680 : checkChunk 1415680 128 = true := by decide +kernel
private theorem c1415808 : checkChunk 1415808 128 = true := by decide +kernel
private theorem c1415936 : checkChunk 1415936 128 = true := by decide +kernel
private theorem c1416064 : checkChunk 1416064 128 = true := by decide +kernel
private theorem c1416192 : checkChunk 1416192 128 = true := by decide +kernel
private theorem c1416320 : checkChunk 1416320 128 = true := by decide +kernel
private theorem c1416448 : checkChunk 1416448 128 = true := by decide +kernel
private theorem c1416576 : checkChunk 1416576 128 = true := by decide +kernel
private theorem c1416704 : checkChunk 1416704 128 = true := by decide +kernel
private theorem c1416832 : checkChunk 1416832 128 = true := by decide +kernel
private theorem c1416960 : checkChunk 1416960 128 = true := by decide +kernel
private theorem c1417088 : checkChunk 1417088 128 = true := by decide +kernel

public theorem checked : Checked 1409024 1417216 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1409024 128 c1409024) (checkChunk_sound 1409152 128 c1409152)) (Checked.append (checkChunk_sound 1409280 128 c1409280) (checkChunk_sound 1409408 128 c1409408))) (Checked.append (Checked.append (checkChunk_sound 1409536 128 c1409536) (checkChunk_sound 1409664 128 c1409664)) (Checked.append (checkChunk_sound 1409792 128 c1409792) (checkChunk_sound 1409920 128 c1409920)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1410048 128 c1410048) (checkChunk_sound 1410176 128 c1410176)) (Checked.append (checkChunk_sound 1410304 128 c1410304) (checkChunk_sound 1410432 128 c1410432))) (Checked.append (Checked.append (checkChunk_sound 1410560 128 c1410560) (checkChunk_sound 1410688 128 c1410688)) (Checked.append (checkChunk_sound 1410816 128 c1410816) (checkChunk_sound 1410944 128 c1410944))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1411072 128 c1411072) (checkChunk_sound 1411200 128 c1411200)) (Checked.append (checkChunk_sound 1411328 128 c1411328) (checkChunk_sound 1411456 128 c1411456))) (Checked.append (Checked.append (checkChunk_sound 1411584 128 c1411584) (checkChunk_sound 1411712 128 c1411712)) (Checked.append (checkChunk_sound 1411840 128 c1411840) (checkChunk_sound 1411968 128 c1411968)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1412096 128 c1412096) (checkChunk_sound 1412224 128 c1412224)) (Checked.append (checkChunk_sound 1412352 128 c1412352) (checkChunk_sound 1412480 128 c1412480))) (Checked.append (Checked.append (checkChunk_sound 1412608 128 c1412608) (checkChunk_sound 1412736 128 c1412736)) (Checked.append (checkChunk_sound 1412864 128 c1412864) (checkChunk_sound 1412992 128 c1412992)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1413120 128 c1413120) (checkChunk_sound 1413248 128 c1413248)) (Checked.append (checkChunk_sound 1413376 128 c1413376) (checkChunk_sound 1413504 128 c1413504))) (Checked.append (Checked.append (checkChunk_sound 1413632 128 c1413632) (checkChunk_sound 1413760 128 c1413760)) (Checked.append (checkChunk_sound 1413888 128 c1413888) (checkChunk_sound 1414016 128 c1414016)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1414144 128 c1414144) (checkChunk_sound 1414272 128 c1414272)) (Checked.append (checkChunk_sound 1414400 128 c1414400) (checkChunk_sound 1414528 128 c1414528))) (Checked.append (Checked.append (checkChunk_sound 1414656 128 c1414656) (checkChunk_sound 1414784 128 c1414784)) (Checked.append (checkChunk_sound 1414912 128 c1414912) (checkChunk_sound 1415040 128 c1415040))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1415168 128 c1415168) (checkChunk_sound 1415296 128 c1415296)) (Checked.append (checkChunk_sound 1415424 128 c1415424) (checkChunk_sound 1415552 128 c1415552))) (Checked.append (Checked.append (checkChunk_sound 1415680 128 c1415680) (checkChunk_sound 1415808 128 c1415808)) (Checked.append (checkChunk_sound 1415936 128 c1415936) (checkChunk_sound 1416064 128 c1416064)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1416192 128 c1416192) (checkChunk_sound 1416320 128 c1416320)) (Checked.append (checkChunk_sound 1416448 128 c1416448) (checkChunk_sound 1416576 128 c1416576))) (Checked.append (Checked.append (checkChunk_sound 1416704 128 c1416704) (checkChunk_sound 1416832 128 c1416832)) (Checked.append (checkChunk_sound 1416960 128 c1416960) (checkChunk_sound 1417088 128 c1417088)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B015
