module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1449984, 1458176).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B020
private theorem c1449984 : checkChunk 1449984 128 = true := by decide +kernel
private theorem c1450112 : checkChunk 1450112 128 = true := by decide +kernel
private theorem c1450240 : checkChunk 1450240 128 = true := by decide +kernel
private theorem c1450368 : checkChunk 1450368 128 = true := by decide +kernel
private theorem c1450496 : checkChunk 1450496 128 = true := by decide +kernel
private theorem c1450624 : checkChunk 1450624 128 = true := by decide +kernel
private theorem c1450752 : checkChunk 1450752 128 = true := by decide +kernel
private theorem c1450880 : checkChunk 1450880 128 = true := by decide +kernel
private theorem c1451008 : checkChunk 1451008 128 = true := by decide +kernel
private theorem c1451136 : checkChunk 1451136 128 = true := by decide +kernel
private theorem c1451264 : checkChunk 1451264 128 = true := by decide +kernel
private theorem c1451392 : checkChunk 1451392 128 = true := by decide +kernel
private theorem c1451520 : checkChunk 1451520 128 = true := by decide +kernel
private theorem c1451648 : checkChunk 1451648 128 = true := by decide +kernel
private theorem c1451776 : checkChunk 1451776 128 = true := by decide +kernel
private theorem c1451904 : checkChunk 1451904 128 = true := by decide +kernel
private theorem c1452032 : checkChunk 1452032 128 = true := by decide +kernel
private theorem c1452160 : checkChunk 1452160 128 = true := by decide +kernel
private theorem c1452288 : checkChunk 1452288 128 = true := by decide +kernel
private theorem c1452416 : checkChunk 1452416 128 = true := by decide +kernel
private theorem c1452544 : checkChunk 1452544 128 = true := by decide +kernel
private theorem c1452672 : checkChunk 1452672 128 = true := by decide +kernel
private theorem c1452800 : checkChunk 1452800 128 = true := by decide +kernel
private theorem c1452928 : checkChunk 1452928 128 = true := by decide +kernel
private theorem c1453056 : checkChunk 1453056 128 = true := by decide +kernel
private theorem c1453184 : checkChunk 1453184 128 = true := by decide +kernel
private theorem c1453312 : checkChunk 1453312 128 = true := by decide +kernel
private theorem c1453440 : checkChunk 1453440 128 = true := by decide +kernel
private theorem c1453568 : checkChunk 1453568 128 = true := by decide +kernel
private theorem c1453696 : checkChunk 1453696 128 = true := by decide +kernel
private theorem c1453824 : checkChunk 1453824 128 = true := by decide +kernel
private theorem c1453952 : checkChunk 1453952 128 = true := by decide +kernel
private theorem c1454080 : checkChunk 1454080 128 = true := by decide +kernel
private theorem c1454208 : checkChunk 1454208 128 = true := by decide +kernel
private theorem c1454336 : checkChunk 1454336 128 = true := by decide +kernel
private theorem c1454464 : checkChunk 1454464 128 = true := by decide +kernel
private theorem c1454592 : checkChunk 1454592 128 = true := by decide +kernel
private theorem c1454720 : checkChunk 1454720 128 = true := by decide +kernel
private theorem c1454848 : checkChunk 1454848 128 = true := by decide +kernel
private theorem c1454976 : checkChunk 1454976 128 = true := by decide +kernel
private theorem c1455104 : checkChunk 1455104 128 = true := by decide +kernel
private theorem c1455232 : checkChunk 1455232 128 = true := by decide +kernel
private theorem c1455360 : checkChunk 1455360 128 = true := by decide +kernel
private theorem c1455488 : checkChunk 1455488 128 = true := by decide +kernel
private theorem c1455616 : checkChunk 1455616 128 = true := by decide +kernel
private theorem c1455744 : checkChunk 1455744 128 = true := by decide +kernel
private theorem c1455872 : checkChunk 1455872 128 = true := by decide +kernel
private theorem c1456000 : checkChunk 1456000 128 = true := by decide +kernel
private theorem c1456128 : checkChunk 1456128 128 = true := by decide +kernel
private theorem c1456256 : checkChunk 1456256 128 = true := by decide +kernel
private theorem c1456384 : checkChunk 1456384 128 = true := by decide +kernel
private theorem c1456512 : checkChunk 1456512 128 = true := by decide +kernel
private theorem c1456640 : checkChunk 1456640 128 = true := by decide +kernel
private theorem c1456768 : checkChunk 1456768 128 = true := by decide +kernel
private theorem c1456896 : checkChunk 1456896 128 = true := by decide +kernel
private theorem c1457024 : checkChunk 1457024 128 = true := by decide +kernel
private theorem c1457152 : checkChunk 1457152 128 = true := by decide +kernel
private theorem c1457280 : checkChunk 1457280 128 = true := by decide +kernel
private theorem c1457408 : checkChunk 1457408 128 = true := by decide +kernel
private theorem c1457536 : checkChunk 1457536 128 = true := by decide +kernel
private theorem c1457664 : checkChunk 1457664 128 = true := by decide +kernel
private theorem c1457792 : checkChunk 1457792 128 = true := by decide +kernel
private theorem c1457920 : checkChunk 1457920 128 = true := by decide +kernel
private theorem c1458048 : checkChunk 1458048 128 = true := by decide +kernel

public theorem checked : Checked 1449984 1458176 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1449984 128 c1449984) (checkChunk_sound 1450112 128 c1450112)) (Checked.append (checkChunk_sound 1450240 128 c1450240) (checkChunk_sound 1450368 128 c1450368))) (Checked.append (Checked.append (checkChunk_sound 1450496 128 c1450496) (checkChunk_sound 1450624 128 c1450624)) (Checked.append (checkChunk_sound 1450752 128 c1450752) (checkChunk_sound 1450880 128 c1450880)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1451008 128 c1451008) (checkChunk_sound 1451136 128 c1451136)) (Checked.append (checkChunk_sound 1451264 128 c1451264) (checkChunk_sound 1451392 128 c1451392))) (Checked.append (Checked.append (checkChunk_sound 1451520 128 c1451520) (checkChunk_sound 1451648 128 c1451648)) (Checked.append (checkChunk_sound 1451776 128 c1451776) (checkChunk_sound 1451904 128 c1451904))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1452032 128 c1452032) (checkChunk_sound 1452160 128 c1452160)) (Checked.append (checkChunk_sound 1452288 128 c1452288) (checkChunk_sound 1452416 128 c1452416))) (Checked.append (Checked.append (checkChunk_sound 1452544 128 c1452544) (checkChunk_sound 1452672 128 c1452672)) (Checked.append (checkChunk_sound 1452800 128 c1452800) (checkChunk_sound 1452928 128 c1452928)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1453056 128 c1453056) (checkChunk_sound 1453184 128 c1453184)) (Checked.append (checkChunk_sound 1453312 128 c1453312) (checkChunk_sound 1453440 128 c1453440))) (Checked.append (Checked.append (checkChunk_sound 1453568 128 c1453568) (checkChunk_sound 1453696 128 c1453696)) (Checked.append (checkChunk_sound 1453824 128 c1453824) (checkChunk_sound 1453952 128 c1453952)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1454080 128 c1454080) (checkChunk_sound 1454208 128 c1454208)) (Checked.append (checkChunk_sound 1454336 128 c1454336) (checkChunk_sound 1454464 128 c1454464))) (Checked.append (Checked.append (checkChunk_sound 1454592 128 c1454592) (checkChunk_sound 1454720 128 c1454720)) (Checked.append (checkChunk_sound 1454848 128 c1454848) (checkChunk_sound 1454976 128 c1454976)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1455104 128 c1455104) (checkChunk_sound 1455232 128 c1455232)) (Checked.append (checkChunk_sound 1455360 128 c1455360) (checkChunk_sound 1455488 128 c1455488))) (Checked.append (Checked.append (checkChunk_sound 1455616 128 c1455616) (checkChunk_sound 1455744 128 c1455744)) (Checked.append (checkChunk_sound 1455872 128 c1455872) (checkChunk_sound 1456000 128 c1456000))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1456128 128 c1456128) (checkChunk_sound 1456256 128 c1456256)) (Checked.append (checkChunk_sound 1456384 128 c1456384) (checkChunk_sound 1456512 128 c1456512))) (Checked.append (Checked.append (checkChunk_sound 1456640 128 c1456640) (checkChunk_sound 1456768 128 c1456768)) (Checked.append (checkChunk_sound 1456896 128 c1456896) (checkChunk_sound 1457024 128 c1457024)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1457152 128 c1457152) (checkChunk_sound 1457280 128 c1457280)) (Checked.append (checkChunk_sound 1457408 128 c1457408) (checkChunk_sound 1457536 128 c1457536))) (Checked.append (Checked.append (checkChunk_sound 1457664 128 c1457664) (checkChunk_sound 1457792 128 c1457792)) (Checked.append (checkChunk_sound 1457920 128 c1457920) (checkChunk_sound 1458048 128 c1458048)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B020
