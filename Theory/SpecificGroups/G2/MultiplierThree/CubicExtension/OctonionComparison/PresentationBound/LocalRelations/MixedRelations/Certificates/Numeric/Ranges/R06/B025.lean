module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1490944, 1499136).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B025
private theorem c1490944 : checkChunk 1490944 128 = true := by decide +kernel
private theorem c1491072 : checkChunk 1491072 128 = true := by decide +kernel
private theorem c1491200 : checkChunk 1491200 128 = true := by decide +kernel
private theorem c1491328 : checkChunk 1491328 128 = true := by decide +kernel
private theorem c1491456 : checkChunk 1491456 128 = true := by decide +kernel
private theorem c1491584 : checkChunk 1491584 128 = true := by decide +kernel
private theorem c1491712 : checkChunk 1491712 128 = true := by decide +kernel
private theorem c1491840 : checkChunk 1491840 128 = true := by decide +kernel
private theorem c1491968 : checkChunk 1491968 128 = true := by decide +kernel
private theorem c1492096 : checkChunk 1492096 128 = true := by decide +kernel
private theorem c1492224 : checkChunk 1492224 128 = true := by decide +kernel
private theorem c1492352 : checkChunk 1492352 128 = true := by decide +kernel
private theorem c1492480 : checkChunk 1492480 128 = true := by decide +kernel
private theorem c1492608 : checkChunk 1492608 128 = true := by decide +kernel
private theorem c1492736 : checkChunk 1492736 128 = true := by decide +kernel
private theorem c1492864 : checkChunk 1492864 128 = true := by decide +kernel
private theorem c1492992 : checkChunk 1492992 128 = true := by decide +kernel
private theorem c1493120 : checkChunk 1493120 128 = true := by decide +kernel
private theorem c1493248 : checkChunk 1493248 128 = true := by decide +kernel
private theorem c1493376 : checkChunk 1493376 128 = true := by decide +kernel
private theorem c1493504 : checkChunk 1493504 128 = true := by decide +kernel
private theorem c1493632 : checkChunk 1493632 128 = true := by decide +kernel
private theorem c1493760 : checkChunk 1493760 128 = true := by decide +kernel
private theorem c1493888 : checkChunk 1493888 128 = true := by decide +kernel
private theorem c1494016 : checkChunk 1494016 128 = true := by decide +kernel
private theorem c1494144 : checkChunk 1494144 128 = true := by decide +kernel
private theorem c1494272 : checkChunk 1494272 128 = true := by decide +kernel
private theorem c1494400 : checkChunk 1494400 128 = true := by decide +kernel
private theorem c1494528 : checkChunk 1494528 128 = true := by decide +kernel
private theorem c1494656 : checkChunk 1494656 128 = true := by decide +kernel
private theorem c1494784 : checkChunk 1494784 128 = true := by decide +kernel
private theorem c1494912 : checkChunk 1494912 128 = true := by decide +kernel
private theorem c1495040 : checkChunk 1495040 128 = true := by decide +kernel
private theorem c1495168 : checkChunk 1495168 128 = true := by decide +kernel
private theorem c1495296 : checkChunk 1495296 128 = true := by decide +kernel
private theorem c1495424 : checkChunk 1495424 128 = true := by decide +kernel
private theorem c1495552 : checkChunk 1495552 128 = true := by decide +kernel
private theorem c1495680 : checkChunk 1495680 128 = true := by decide +kernel
private theorem c1495808 : checkChunk 1495808 128 = true := by decide +kernel
private theorem c1495936 : checkChunk 1495936 128 = true := by decide +kernel
private theorem c1496064 : checkChunk 1496064 128 = true := by decide +kernel
private theorem c1496192 : checkChunk 1496192 128 = true := by decide +kernel
private theorem c1496320 : checkChunk 1496320 128 = true := by decide +kernel
private theorem c1496448 : checkChunk 1496448 128 = true := by decide +kernel
private theorem c1496576 : checkChunk 1496576 128 = true := by decide +kernel
private theorem c1496704 : checkChunk 1496704 128 = true := by decide +kernel
private theorem c1496832 : checkChunk 1496832 128 = true := by decide +kernel
private theorem c1496960 : checkChunk 1496960 128 = true := by decide +kernel
private theorem c1497088 : checkChunk 1497088 128 = true := by decide +kernel
private theorem c1497216 : checkChunk 1497216 128 = true := by decide +kernel
private theorem c1497344 : checkChunk 1497344 128 = true := by decide +kernel
private theorem c1497472 : checkChunk 1497472 128 = true := by decide +kernel
private theorem c1497600 : checkChunk 1497600 128 = true := by decide +kernel
private theorem c1497728 : checkChunk 1497728 128 = true := by decide +kernel
private theorem c1497856 : checkChunk 1497856 128 = true := by decide +kernel
private theorem c1497984 : checkChunk 1497984 128 = true := by decide +kernel
private theorem c1498112 : checkChunk 1498112 128 = true := by decide +kernel
private theorem c1498240 : checkChunk 1498240 128 = true := by decide +kernel
private theorem c1498368 : checkChunk 1498368 128 = true := by decide +kernel
private theorem c1498496 : checkChunk 1498496 128 = true := by decide +kernel
private theorem c1498624 : checkChunk 1498624 128 = true := by decide +kernel
private theorem c1498752 : checkChunk 1498752 128 = true := by decide +kernel
private theorem c1498880 : checkChunk 1498880 128 = true := by decide +kernel
private theorem c1499008 : checkChunk 1499008 128 = true := by decide +kernel

public theorem checked : Checked 1490944 1499136 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1490944 128 c1490944) (checkChunk_sound 1491072 128 c1491072)) (Checked.append (checkChunk_sound 1491200 128 c1491200) (checkChunk_sound 1491328 128 c1491328))) (Checked.append (Checked.append (checkChunk_sound 1491456 128 c1491456) (checkChunk_sound 1491584 128 c1491584)) (Checked.append (checkChunk_sound 1491712 128 c1491712) (checkChunk_sound 1491840 128 c1491840)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1491968 128 c1491968) (checkChunk_sound 1492096 128 c1492096)) (Checked.append (checkChunk_sound 1492224 128 c1492224) (checkChunk_sound 1492352 128 c1492352))) (Checked.append (Checked.append (checkChunk_sound 1492480 128 c1492480) (checkChunk_sound 1492608 128 c1492608)) (Checked.append (checkChunk_sound 1492736 128 c1492736) (checkChunk_sound 1492864 128 c1492864))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1492992 128 c1492992) (checkChunk_sound 1493120 128 c1493120)) (Checked.append (checkChunk_sound 1493248 128 c1493248) (checkChunk_sound 1493376 128 c1493376))) (Checked.append (Checked.append (checkChunk_sound 1493504 128 c1493504) (checkChunk_sound 1493632 128 c1493632)) (Checked.append (checkChunk_sound 1493760 128 c1493760) (checkChunk_sound 1493888 128 c1493888)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1494016 128 c1494016) (checkChunk_sound 1494144 128 c1494144)) (Checked.append (checkChunk_sound 1494272 128 c1494272) (checkChunk_sound 1494400 128 c1494400))) (Checked.append (Checked.append (checkChunk_sound 1494528 128 c1494528) (checkChunk_sound 1494656 128 c1494656)) (Checked.append (checkChunk_sound 1494784 128 c1494784) (checkChunk_sound 1494912 128 c1494912)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1495040 128 c1495040) (checkChunk_sound 1495168 128 c1495168)) (Checked.append (checkChunk_sound 1495296 128 c1495296) (checkChunk_sound 1495424 128 c1495424))) (Checked.append (Checked.append (checkChunk_sound 1495552 128 c1495552) (checkChunk_sound 1495680 128 c1495680)) (Checked.append (checkChunk_sound 1495808 128 c1495808) (checkChunk_sound 1495936 128 c1495936)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1496064 128 c1496064) (checkChunk_sound 1496192 128 c1496192)) (Checked.append (checkChunk_sound 1496320 128 c1496320) (checkChunk_sound 1496448 128 c1496448))) (Checked.append (Checked.append (checkChunk_sound 1496576 128 c1496576) (checkChunk_sound 1496704 128 c1496704)) (Checked.append (checkChunk_sound 1496832 128 c1496832) (checkChunk_sound 1496960 128 c1496960))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1497088 128 c1497088) (checkChunk_sound 1497216 128 c1497216)) (Checked.append (checkChunk_sound 1497344 128 c1497344) (checkChunk_sound 1497472 128 c1497472))) (Checked.append (Checked.append (checkChunk_sound 1497600 128 c1497600) (checkChunk_sound 1497728 128 c1497728)) (Checked.append (checkChunk_sound 1497856 128 c1497856) (checkChunk_sound 1497984 128 c1497984)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1498112 128 c1498112) (checkChunk_sound 1498240 128 c1498240)) (Checked.append (checkChunk_sound 1498368 128 c1498368) (checkChunk_sound 1498496 128 c1498496))) (Checked.append (Checked.append (checkChunk_sound 1498624 128 c1498624) (checkChunk_sound 1498752 128 c1498752)) (Checked.append (checkChunk_sound 1498880 128 c1498880) (checkChunk_sound 1499008 128 c1499008)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B025
