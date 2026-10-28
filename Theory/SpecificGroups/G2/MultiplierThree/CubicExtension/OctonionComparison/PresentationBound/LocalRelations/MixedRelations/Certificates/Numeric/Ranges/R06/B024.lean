module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1482752, 1490944).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B024
private theorem c1482752 : checkChunk 1482752 128 = true := by decide +kernel
private theorem c1482880 : checkChunk 1482880 128 = true := by decide +kernel
private theorem c1483008 : checkChunk 1483008 128 = true := by decide +kernel
private theorem c1483136 : checkChunk 1483136 128 = true := by decide +kernel
private theorem c1483264 : checkChunk 1483264 128 = true := by decide +kernel
private theorem c1483392 : checkChunk 1483392 128 = true := by decide +kernel
private theorem c1483520 : checkChunk 1483520 128 = true := by decide +kernel
private theorem c1483648 : checkChunk 1483648 128 = true := by decide +kernel
private theorem c1483776 : checkChunk 1483776 128 = true := by decide +kernel
private theorem c1483904 : checkChunk 1483904 128 = true := by decide +kernel
private theorem c1484032 : checkChunk 1484032 128 = true := by decide +kernel
private theorem c1484160 : checkChunk 1484160 128 = true := by decide +kernel
private theorem c1484288 : checkChunk 1484288 128 = true := by decide +kernel
private theorem c1484416 : checkChunk 1484416 128 = true := by decide +kernel
private theorem c1484544 : checkChunk 1484544 128 = true := by decide +kernel
private theorem c1484672 : checkChunk 1484672 128 = true := by decide +kernel
private theorem c1484800 : checkChunk 1484800 128 = true := by decide +kernel
private theorem c1484928 : checkChunk 1484928 128 = true := by decide +kernel
private theorem c1485056 : checkChunk 1485056 128 = true := by decide +kernel
private theorem c1485184 : checkChunk 1485184 128 = true := by decide +kernel
private theorem c1485312 : checkChunk 1485312 128 = true := by decide +kernel
private theorem c1485440 : checkChunk 1485440 128 = true := by decide +kernel
private theorem c1485568 : checkChunk 1485568 128 = true := by decide +kernel
private theorem c1485696 : checkChunk 1485696 128 = true := by decide +kernel
private theorem c1485824 : checkChunk 1485824 128 = true := by decide +kernel
private theorem c1485952 : checkChunk 1485952 128 = true := by decide +kernel
private theorem c1486080 : checkChunk 1486080 128 = true := by decide +kernel
private theorem c1486208 : checkChunk 1486208 128 = true := by decide +kernel
private theorem c1486336 : checkChunk 1486336 128 = true := by decide +kernel
private theorem c1486464 : checkChunk 1486464 128 = true := by decide +kernel
private theorem c1486592 : checkChunk 1486592 128 = true := by decide +kernel
private theorem c1486720 : checkChunk 1486720 128 = true := by decide +kernel
private theorem c1486848 : checkChunk 1486848 128 = true := by decide +kernel
private theorem c1486976 : checkChunk 1486976 128 = true := by decide +kernel
private theorem c1487104 : checkChunk 1487104 128 = true := by decide +kernel
private theorem c1487232 : checkChunk 1487232 128 = true := by decide +kernel
private theorem c1487360 : checkChunk 1487360 128 = true := by decide +kernel
private theorem c1487488 : checkChunk 1487488 128 = true := by decide +kernel
private theorem c1487616 : checkChunk 1487616 128 = true := by decide +kernel
private theorem c1487744 : checkChunk 1487744 128 = true := by decide +kernel
private theorem c1487872 : checkChunk 1487872 128 = true := by decide +kernel
private theorem c1488000 : checkChunk 1488000 128 = true := by decide +kernel
private theorem c1488128 : checkChunk 1488128 128 = true := by decide +kernel
private theorem c1488256 : checkChunk 1488256 128 = true := by decide +kernel
private theorem c1488384 : checkChunk 1488384 128 = true := by decide +kernel
private theorem c1488512 : checkChunk 1488512 128 = true := by decide +kernel
private theorem c1488640 : checkChunk 1488640 128 = true := by decide +kernel
private theorem c1488768 : checkChunk 1488768 128 = true := by decide +kernel
private theorem c1488896 : checkChunk 1488896 128 = true := by decide +kernel
private theorem c1489024 : checkChunk 1489024 128 = true := by decide +kernel
private theorem c1489152 : checkChunk 1489152 128 = true := by decide +kernel
private theorem c1489280 : checkChunk 1489280 128 = true := by decide +kernel
private theorem c1489408 : checkChunk 1489408 128 = true := by decide +kernel
private theorem c1489536 : checkChunk 1489536 128 = true := by decide +kernel
private theorem c1489664 : checkChunk 1489664 128 = true := by decide +kernel
private theorem c1489792 : checkChunk 1489792 128 = true := by decide +kernel
private theorem c1489920 : checkChunk 1489920 128 = true := by decide +kernel
private theorem c1490048 : checkChunk 1490048 128 = true := by decide +kernel
private theorem c1490176 : checkChunk 1490176 128 = true := by decide +kernel
private theorem c1490304 : checkChunk 1490304 128 = true := by decide +kernel
private theorem c1490432 : checkChunk 1490432 128 = true := by decide +kernel
private theorem c1490560 : checkChunk 1490560 128 = true := by decide +kernel
private theorem c1490688 : checkChunk 1490688 128 = true := by decide +kernel
private theorem c1490816 : checkChunk 1490816 128 = true := by decide +kernel

public theorem checked : Checked 1482752 1490944 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1482752 128 c1482752) (checkChunk_sound 1482880 128 c1482880)) (Checked.append (checkChunk_sound 1483008 128 c1483008) (checkChunk_sound 1483136 128 c1483136))) (Checked.append (Checked.append (checkChunk_sound 1483264 128 c1483264) (checkChunk_sound 1483392 128 c1483392)) (Checked.append (checkChunk_sound 1483520 128 c1483520) (checkChunk_sound 1483648 128 c1483648)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1483776 128 c1483776) (checkChunk_sound 1483904 128 c1483904)) (Checked.append (checkChunk_sound 1484032 128 c1484032) (checkChunk_sound 1484160 128 c1484160))) (Checked.append (Checked.append (checkChunk_sound 1484288 128 c1484288) (checkChunk_sound 1484416 128 c1484416)) (Checked.append (checkChunk_sound 1484544 128 c1484544) (checkChunk_sound 1484672 128 c1484672))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1484800 128 c1484800) (checkChunk_sound 1484928 128 c1484928)) (Checked.append (checkChunk_sound 1485056 128 c1485056) (checkChunk_sound 1485184 128 c1485184))) (Checked.append (Checked.append (checkChunk_sound 1485312 128 c1485312) (checkChunk_sound 1485440 128 c1485440)) (Checked.append (checkChunk_sound 1485568 128 c1485568) (checkChunk_sound 1485696 128 c1485696)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1485824 128 c1485824) (checkChunk_sound 1485952 128 c1485952)) (Checked.append (checkChunk_sound 1486080 128 c1486080) (checkChunk_sound 1486208 128 c1486208))) (Checked.append (Checked.append (checkChunk_sound 1486336 128 c1486336) (checkChunk_sound 1486464 128 c1486464)) (Checked.append (checkChunk_sound 1486592 128 c1486592) (checkChunk_sound 1486720 128 c1486720)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1486848 128 c1486848) (checkChunk_sound 1486976 128 c1486976)) (Checked.append (checkChunk_sound 1487104 128 c1487104) (checkChunk_sound 1487232 128 c1487232))) (Checked.append (Checked.append (checkChunk_sound 1487360 128 c1487360) (checkChunk_sound 1487488 128 c1487488)) (Checked.append (checkChunk_sound 1487616 128 c1487616) (checkChunk_sound 1487744 128 c1487744)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1487872 128 c1487872) (checkChunk_sound 1488000 128 c1488000)) (Checked.append (checkChunk_sound 1488128 128 c1488128) (checkChunk_sound 1488256 128 c1488256))) (Checked.append (Checked.append (checkChunk_sound 1488384 128 c1488384) (checkChunk_sound 1488512 128 c1488512)) (Checked.append (checkChunk_sound 1488640 128 c1488640) (checkChunk_sound 1488768 128 c1488768))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1488896 128 c1488896) (checkChunk_sound 1489024 128 c1489024)) (Checked.append (checkChunk_sound 1489152 128 c1489152) (checkChunk_sound 1489280 128 c1489280))) (Checked.append (Checked.append (checkChunk_sound 1489408 128 c1489408) (checkChunk_sound 1489536 128 c1489536)) (Checked.append (checkChunk_sound 1489664 128 c1489664) (checkChunk_sound 1489792 128 c1489792)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1489920 128 c1489920) (checkChunk_sound 1490048 128 c1490048)) (Checked.append (checkChunk_sound 1490176 128 c1490176) (checkChunk_sound 1490304 128 c1490304))) (Checked.append (Checked.append (checkChunk_sound 1490432 128 c1490432) (checkChunk_sound 1490560 128 c1490560)) (Checked.append (checkChunk_sound 1490688 128 c1490688) (checkChunk_sound 1490816 128 c1490816)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B024
