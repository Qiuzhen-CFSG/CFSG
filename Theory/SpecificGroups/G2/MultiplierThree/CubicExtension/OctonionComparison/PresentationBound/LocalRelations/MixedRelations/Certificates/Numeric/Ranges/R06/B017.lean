module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1425408, 1433600).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B017
private theorem c1425408 : checkChunk 1425408 128 = true := by decide +kernel
private theorem c1425536 : checkChunk 1425536 128 = true := by decide +kernel
private theorem c1425664 : checkChunk 1425664 128 = true := by decide +kernel
private theorem c1425792 : checkChunk 1425792 128 = true := by decide +kernel
private theorem c1425920 : checkChunk 1425920 128 = true := by decide +kernel
private theorem c1426048 : checkChunk 1426048 128 = true := by decide +kernel
private theorem c1426176 : checkChunk 1426176 128 = true := by decide +kernel
private theorem c1426304 : checkChunk 1426304 128 = true := by decide +kernel
private theorem c1426432 : checkChunk 1426432 128 = true := by decide +kernel
private theorem c1426560 : checkChunk 1426560 128 = true := by decide +kernel
private theorem c1426688 : checkChunk 1426688 128 = true := by decide +kernel
private theorem c1426816 : checkChunk 1426816 128 = true := by decide +kernel
private theorem c1426944 : checkChunk 1426944 128 = true := by decide +kernel
private theorem c1427072 : checkChunk 1427072 128 = true := by decide +kernel
private theorem c1427200 : checkChunk 1427200 128 = true := by decide +kernel
private theorem c1427328 : checkChunk 1427328 128 = true := by decide +kernel
private theorem c1427456 : checkChunk 1427456 128 = true := by decide +kernel
private theorem c1427584 : checkChunk 1427584 128 = true := by decide +kernel
private theorem c1427712 : checkChunk 1427712 128 = true := by decide +kernel
private theorem c1427840 : checkChunk 1427840 128 = true := by decide +kernel
private theorem c1427968 : checkChunk 1427968 128 = true := by decide +kernel
private theorem c1428096 : checkChunk 1428096 128 = true := by decide +kernel
private theorem c1428224 : checkChunk 1428224 128 = true := by decide +kernel
private theorem c1428352 : checkChunk 1428352 128 = true := by decide +kernel
private theorem c1428480 : checkChunk 1428480 128 = true := by decide +kernel
private theorem c1428608 : checkChunk 1428608 128 = true := by decide +kernel
private theorem c1428736 : checkChunk 1428736 128 = true := by decide +kernel
private theorem c1428864 : checkChunk 1428864 128 = true := by decide +kernel
private theorem c1428992 : checkChunk 1428992 128 = true := by decide +kernel
private theorem c1429120 : checkChunk 1429120 128 = true := by decide +kernel
private theorem c1429248 : checkChunk 1429248 128 = true := by decide +kernel
private theorem c1429376 : checkChunk 1429376 128 = true := by decide +kernel
private theorem c1429504 : checkChunk 1429504 128 = true := by decide +kernel
private theorem c1429632 : checkChunk 1429632 128 = true := by decide +kernel
private theorem c1429760 : checkChunk 1429760 128 = true := by decide +kernel
private theorem c1429888 : checkChunk 1429888 128 = true := by decide +kernel
private theorem c1430016 : checkChunk 1430016 128 = true := by decide +kernel
private theorem c1430144 : checkChunk 1430144 128 = true := by decide +kernel
private theorem c1430272 : checkChunk 1430272 128 = true := by decide +kernel
private theorem c1430400 : checkChunk 1430400 128 = true := by decide +kernel
private theorem c1430528 : checkChunk 1430528 128 = true := by decide +kernel
private theorem c1430656 : checkChunk 1430656 128 = true := by decide +kernel
private theorem c1430784 : checkChunk 1430784 128 = true := by decide +kernel
private theorem c1430912 : checkChunk 1430912 128 = true := by decide +kernel
private theorem c1431040 : checkChunk 1431040 128 = true := by decide +kernel
private theorem c1431168 : checkChunk 1431168 128 = true := by decide +kernel
private theorem c1431296 : checkChunk 1431296 128 = true := by decide +kernel
private theorem c1431424 : checkChunk 1431424 128 = true := by decide +kernel
private theorem c1431552 : checkChunk 1431552 128 = true := by decide +kernel
private theorem c1431680 : checkChunk 1431680 128 = true := by decide +kernel
private theorem c1431808 : checkChunk 1431808 128 = true := by decide +kernel
private theorem c1431936 : checkChunk 1431936 128 = true := by decide +kernel
private theorem c1432064 : checkChunk 1432064 128 = true := by decide +kernel
private theorem c1432192 : checkChunk 1432192 128 = true := by decide +kernel
private theorem c1432320 : checkChunk 1432320 128 = true := by decide +kernel
private theorem c1432448 : checkChunk 1432448 128 = true := by decide +kernel
private theorem c1432576 : checkChunk 1432576 128 = true := by decide +kernel
private theorem c1432704 : checkChunk 1432704 128 = true := by decide +kernel
private theorem c1432832 : checkChunk 1432832 128 = true := by decide +kernel
private theorem c1432960 : checkChunk 1432960 128 = true := by decide +kernel
private theorem c1433088 : checkChunk 1433088 128 = true := by decide +kernel
private theorem c1433216 : checkChunk 1433216 128 = true := by decide +kernel
private theorem c1433344 : checkChunk 1433344 128 = true := by decide +kernel
private theorem c1433472 : checkChunk 1433472 128 = true := by decide +kernel

public theorem checked : Checked 1425408 1433600 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1425408 128 c1425408) (checkChunk_sound 1425536 128 c1425536)) (Checked.append (checkChunk_sound 1425664 128 c1425664) (checkChunk_sound 1425792 128 c1425792))) (Checked.append (Checked.append (checkChunk_sound 1425920 128 c1425920) (checkChunk_sound 1426048 128 c1426048)) (Checked.append (checkChunk_sound 1426176 128 c1426176) (checkChunk_sound 1426304 128 c1426304)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1426432 128 c1426432) (checkChunk_sound 1426560 128 c1426560)) (Checked.append (checkChunk_sound 1426688 128 c1426688) (checkChunk_sound 1426816 128 c1426816))) (Checked.append (Checked.append (checkChunk_sound 1426944 128 c1426944) (checkChunk_sound 1427072 128 c1427072)) (Checked.append (checkChunk_sound 1427200 128 c1427200) (checkChunk_sound 1427328 128 c1427328))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1427456 128 c1427456) (checkChunk_sound 1427584 128 c1427584)) (Checked.append (checkChunk_sound 1427712 128 c1427712) (checkChunk_sound 1427840 128 c1427840))) (Checked.append (Checked.append (checkChunk_sound 1427968 128 c1427968) (checkChunk_sound 1428096 128 c1428096)) (Checked.append (checkChunk_sound 1428224 128 c1428224) (checkChunk_sound 1428352 128 c1428352)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1428480 128 c1428480) (checkChunk_sound 1428608 128 c1428608)) (Checked.append (checkChunk_sound 1428736 128 c1428736) (checkChunk_sound 1428864 128 c1428864))) (Checked.append (Checked.append (checkChunk_sound 1428992 128 c1428992) (checkChunk_sound 1429120 128 c1429120)) (Checked.append (checkChunk_sound 1429248 128 c1429248) (checkChunk_sound 1429376 128 c1429376)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1429504 128 c1429504) (checkChunk_sound 1429632 128 c1429632)) (Checked.append (checkChunk_sound 1429760 128 c1429760) (checkChunk_sound 1429888 128 c1429888))) (Checked.append (Checked.append (checkChunk_sound 1430016 128 c1430016) (checkChunk_sound 1430144 128 c1430144)) (Checked.append (checkChunk_sound 1430272 128 c1430272) (checkChunk_sound 1430400 128 c1430400)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1430528 128 c1430528) (checkChunk_sound 1430656 128 c1430656)) (Checked.append (checkChunk_sound 1430784 128 c1430784) (checkChunk_sound 1430912 128 c1430912))) (Checked.append (Checked.append (checkChunk_sound 1431040 128 c1431040) (checkChunk_sound 1431168 128 c1431168)) (Checked.append (checkChunk_sound 1431296 128 c1431296) (checkChunk_sound 1431424 128 c1431424))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1431552 128 c1431552) (checkChunk_sound 1431680 128 c1431680)) (Checked.append (checkChunk_sound 1431808 128 c1431808) (checkChunk_sound 1431936 128 c1431936))) (Checked.append (Checked.append (checkChunk_sound 1432064 128 c1432064) (checkChunk_sound 1432192 128 c1432192)) (Checked.append (checkChunk_sound 1432320 128 c1432320) (checkChunk_sound 1432448 128 c1432448)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1432576 128 c1432576) (checkChunk_sound 1432704 128 c1432704)) (Checked.append (checkChunk_sound 1432832 128 c1432832) (checkChunk_sound 1432960 128 c1432960))) (Checked.append (Checked.append (checkChunk_sound 1433088 128 c1433088) (checkChunk_sound 1433216 128 c1433216)) (Checked.append (checkChunk_sound 1433344 128 c1433344) (checkChunk_sound 1433472 128 c1433472)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B017
