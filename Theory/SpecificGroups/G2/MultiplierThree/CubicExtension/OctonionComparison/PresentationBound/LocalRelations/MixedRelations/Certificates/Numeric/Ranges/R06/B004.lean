module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1318912, 1327104).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B004
private theorem c1318912 : checkChunk 1318912 128 = true := by decide +kernel
private theorem c1319040 : checkChunk 1319040 128 = true := by decide +kernel
private theorem c1319168 : checkChunk 1319168 128 = true := by decide +kernel
private theorem c1319296 : checkChunk 1319296 128 = true := by decide +kernel
private theorem c1319424 : checkChunk 1319424 128 = true := by decide +kernel
private theorem c1319552 : checkChunk 1319552 128 = true := by decide +kernel
private theorem c1319680 : checkChunk 1319680 128 = true := by decide +kernel
private theorem c1319808 : checkChunk 1319808 128 = true := by decide +kernel
private theorem c1319936 : checkChunk 1319936 128 = true := by decide +kernel
private theorem c1320064 : checkChunk 1320064 128 = true := by decide +kernel
private theorem c1320192 : checkChunk 1320192 128 = true := by decide +kernel
private theorem c1320320 : checkChunk 1320320 128 = true := by decide +kernel
private theorem c1320448 : checkChunk 1320448 128 = true := by decide +kernel
private theorem c1320576 : checkChunk 1320576 128 = true := by decide +kernel
private theorem c1320704 : checkChunk 1320704 128 = true := by decide +kernel
private theorem c1320832 : checkChunk 1320832 128 = true := by decide +kernel
private theorem c1320960 : checkChunk 1320960 128 = true := by decide +kernel
private theorem c1321088 : checkChunk 1321088 128 = true := by decide +kernel
private theorem c1321216 : checkChunk 1321216 128 = true := by decide +kernel
private theorem c1321344 : checkChunk 1321344 128 = true := by decide +kernel
private theorem c1321472 : checkChunk 1321472 128 = true := by decide +kernel
private theorem c1321600 : checkChunk 1321600 128 = true := by decide +kernel
private theorem c1321728 : checkChunk 1321728 128 = true := by decide +kernel
private theorem c1321856 : checkChunk 1321856 128 = true := by decide +kernel
private theorem c1321984 : checkChunk 1321984 128 = true := by decide +kernel
private theorem c1322112 : checkChunk 1322112 128 = true := by decide +kernel
private theorem c1322240 : checkChunk 1322240 128 = true := by decide +kernel
private theorem c1322368 : checkChunk 1322368 128 = true := by decide +kernel
private theorem c1322496 : checkChunk 1322496 128 = true := by decide +kernel
private theorem c1322624 : checkChunk 1322624 128 = true := by decide +kernel
private theorem c1322752 : checkChunk 1322752 128 = true := by decide +kernel
private theorem c1322880 : checkChunk 1322880 128 = true := by decide +kernel
private theorem c1323008 : checkChunk 1323008 128 = true := by decide +kernel
private theorem c1323136 : checkChunk 1323136 128 = true := by decide +kernel
private theorem c1323264 : checkChunk 1323264 128 = true := by decide +kernel
private theorem c1323392 : checkChunk 1323392 128 = true := by decide +kernel
private theorem c1323520 : checkChunk 1323520 128 = true := by decide +kernel
private theorem c1323648 : checkChunk 1323648 128 = true := by decide +kernel
private theorem c1323776 : checkChunk 1323776 128 = true := by decide +kernel
private theorem c1323904 : checkChunk 1323904 128 = true := by decide +kernel
private theorem c1324032 : checkChunk 1324032 128 = true := by decide +kernel
private theorem c1324160 : checkChunk 1324160 128 = true := by decide +kernel
private theorem c1324288 : checkChunk 1324288 128 = true := by decide +kernel
private theorem c1324416 : checkChunk 1324416 128 = true := by decide +kernel
private theorem c1324544 : checkChunk 1324544 128 = true := by decide +kernel
private theorem c1324672 : checkChunk 1324672 128 = true := by decide +kernel
private theorem c1324800 : checkChunk 1324800 128 = true := by decide +kernel
private theorem c1324928 : checkChunk 1324928 128 = true := by decide +kernel
private theorem c1325056 : checkChunk 1325056 128 = true := by decide +kernel
private theorem c1325184 : checkChunk 1325184 128 = true := by decide +kernel
private theorem c1325312 : checkChunk 1325312 128 = true := by decide +kernel
private theorem c1325440 : checkChunk 1325440 128 = true := by decide +kernel
private theorem c1325568 : checkChunk 1325568 128 = true := by decide +kernel
private theorem c1325696 : checkChunk 1325696 128 = true := by decide +kernel
private theorem c1325824 : checkChunk 1325824 128 = true := by decide +kernel
private theorem c1325952 : checkChunk 1325952 128 = true := by decide +kernel
private theorem c1326080 : checkChunk 1326080 128 = true := by decide +kernel
private theorem c1326208 : checkChunk 1326208 128 = true := by decide +kernel
private theorem c1326336 : checkChunk 1326336 128 = true := by decide +kernel
private theorem c1326464 : checkChunk 1326464 128 = true := by decide +kernel
private theorem c1326592 : checkChunk 1326592 128 = true := by decide +kernel
private theorem c1326720 : checkChunk 1326720 128 = true := by decide +kernel
private theorem c1326848 : checkChunk 1326848 128 = true := by decide +kernel
private theorem c1326976 : checkChunk 1326976 128 = true := by decide +kernel

public theorem checked : Checked 1318912 1327104 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1318912 128 c1318912) (checkChunk_sound 1319040 128 c1319040)) (Checked.append (checkChunk_sound 1319168 128 c1319168) (checkChunk_sound 1319296 128 c1319296))) (Checked.append (Checked.append (checkChunk_sound 1319424 128 c1319424) (checkChunk_sound 1319552 128 c1319552)) (Checked.append (checkChunk_sound 1319680 128 c1319680) (checkChunk_sound 1319808 128 c1319808)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1319936 128 c1319936) (checkChunk_sound 1320064 128 c1320064)) (Checked.append (checkChunk_sound 1320192 128 c1320192) (checkChunk_sound 1320320 128 c1320320))) (Checked.append (Checked.append (checkChunk_sound 1320448 128 c1320448) (checkChunk_sound 1320576 128 c1320576)) (Checked.append (checkChunk_sound 1320704 128 c1320704) (checkChunk_sound 1320832 128 c1320832))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1320960 128 c1320960) (checkChunk_sound 1321088 128 c1321088)) (Checked.append (checkChunk_sound 1321216 128 c1321216) (checkChunk_sound 1321344 128 c1321344))) (Checked.append (Checked.append (checkChunk_sound 1321472 128 c1321472) (checkChunk_sound 1321600 128 c1321600)) (Checked.append (checkChunk_sound 1321728 128 c1321728) (checkChunk_sound 1321856 128 c1321856)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1321984 128 c1321984) (checkChunk_sound 1322112 128 c1322112)) (Checked.append (checkChunk_sound 1322240 128 c1322240) (checkChunk_sound 1322368 128 c1322368))) (Checked.append (Checked.append (checkChunk_sound 1322496 128 c1322496) (checkChunk_sound 1322624 128 c1322624)) (Checked.append (checkChunk_sound 1322752 128 c1322752) (checkChunk_sound 1322880 128 c1322880)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1323008 128 c1323008) (checkChunk_sound 1323136 128 c1323136)) (Checked.append (checkChunk_sound 1323264 128 c1323264) (checkChunk_sound 1323392 128 c1323392))) (Checked.append (Checked.append (checkChunk_sound 1323520 128 c1323520) (checkChunk_sound 1323648 128 c1323648)) (Checked.append (checkChunk_sound 1323776 128 c1323776) (checkChunk_sound 1323904 128 c1323904)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1324032 128 c1324032) (checkChunk_sound 1324160 128 c1324160)) (Checked.append (checkChunk_sound 1324288 128 c1324288) (checkChunk_sound 1324416 128 c1324416))) (Checked.append (Checked.append (checkChunk_sound 1324544 128 c1324544) (checkChunk_sound 1324672 128 c1324672)) (Checked.append (checkChunk_sound 1324800 128 c1324800) (checkChunk_sound 1324928 128 c1324928))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1325056 128 c1325056) (checkChunk_sound 1325184 128 c1325184)) (Checked.append (checkChunk_sound 1325312 128 c1325312) (checkChunk_sound 1325440 128 c1325440))) (Checked.append (Checked.append (checkChunk_sound 1325568 128 c1325568) (checkChunk_sound 1325696 128 c1325696)) (Checked.append (checkChunk_sound 1325824 128 c1325824) (checkChunk_sound 1325952 128 c1325952)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1326080 128 c1326080) (checkChunk_sound 1326208 128 c1326208)) (Checked.append (checkChunk_sound 1326336 128 c1326336) (checkChunk_sound 1326464 128 c1326464))) (Checked.append (Checked.append (checkChunk_sound 1326592 128 c1326592) (checkChunk_sound 1326720 128 c1326720)) (Checked.append (checkChunk_sound 1326848 128 c1326848) (checkChunk_sound 1326976 128 c1326976)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B004
