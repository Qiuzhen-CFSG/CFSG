module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1458176, 1466368).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B021
private theorem c1458176 : checkChunk 1458176 128 = true := by decide +kernel
private theorem c1458304 : checkChunk 1458304 128 = true := by decide +kernel
private theorem c1458432 : checkChunk 1458432 128 = true := by decide +kernel
private theorem c1458560 : checkChunk 1458560 128 = true := by decide +kernel
private theorem c1458688 : checkChunk 1458688 128 = true := by decide +kernel
private theorem c1458816 : checkChunk 1458816 128 = true := by decide +kernel
private theorem c1458944 : checkChunk 1458944 128 = true := by decide +kernel
private theorem c1459072 : checkChunk 1459072 128 = true := by decide +kernel
private theorem c1459200 : checkChunk 1459200 128 = true := by decide +kernel
private theorem c1459328 : checkChunk 1459328 128 = true := by decide +kernel
private theorem c1459456 : checkChunk 1459456 128 = true := by decide +kernel
private theorem c1459584 : checkChunk 1459584 128 = true := by decide +kernel
private theorem c1459712 : checkChunk 1459712 128 = true := by decide +kernel
private theorem c1459840 : checkChunk 1459840 128 = true := by decide +kernel
private theorem c1459968 : checkChunk 1459968 128 = true := by decide +kernel
private theorem c1460096 : checkChunk 1460096 128 = true := by decide +kernel
private theorem c1460224 : checkChunk 1460224 128 = true := by decide +kernel
private theorem c1460352 : checkChunk 1460352 128 = true := by decide +kernel
private theorem c1460480 : checkChunk 1460480 128 = true := by decide +kernel
private theorem c1460608 : checkChunk 1460608 128 = true := by decide +kernel
private theorem c1460736 : checkChunk 1460736 128 = true := by decide +kernel
private theorem c1460864 : checkChunk 1460864 128 = true := by decide +kernel
private theorem c1460992 : checkChunk 1460992 128 = true := by decide +kernel
private theorem c1461120 : checkChunk 1461120 128 = true := by decide +kernel
private theorem c1461248 : checkChunk 1461248 128 = true := by decide +kernel
private theorem c1461376 : checkChunk 1461376 128 = true := by decide +kernel
private theorem c1461504 : checkChunk 1461504 128 = true := by decide +kernel
private theorem c1461632 : checkChunk 1461632 128 = true := by decide +kernel
private theorem c1461760 : checkChunk 1461760 128 = true := by decide +kernel
private theorem c1461888 : checkChunk 1461888 128 = true := by decide +kernel
private theorem c1462016 : checkChunk 1462016 128 = true := by decide +kernel
private theorem c1462144 : checkChunk 1462144 128 = true := by decide +kernel
private theorem c1462272 : checkChunk 1462272 128 = true := by decide +kernel
private theorem c1462400 : checkChunk 1462400 128 = true := by decide +kernel
private theorem c1462528 : checkChunk 1462528 128 = true := by decide +kernel
private theorem c1462656 : checkChunk 1462656 128 = true := by decide +kernel
private theorem c1462784 : checkChunk 1462784 128 = true := by decide +kernel
private theorem c1462912 : checkChunk 1462912 128 = true := by decide +kernel
private theorem c1463040 : checkChunk 1463040 128 = true := by decide +kernel
private theorem c1463168 : checkChunk 1463168 128 = true := by decide +kernel
private theorem c1463296 : checkChunk 1463296 128 = true := by decide +kernel
private theorem c1463424 : checkChunk 1463424 128 = true := by decide +kernel
private theorem c1463552 : checkChunk 1463552 128 = true := by decide +kernel
private theorem c1463680 : checkChunk 1463680 128 = true := by decide +kernel
private theorem c1463808 : checkChunk 1463808 128 = true := by decide +kernel
private theorem c1463936 : checkChunk 1463936 128 = true := by decide +kernel
private theorem c1464064 : checkChunk 1464064 128 = true := by decide +kernel
private theorem c1464192 : checkChunk 1464192 128 = true := by decide +kernel
private theorem c1464320 : checkChunk 1464320 128 = true := by decide +kernel
private theorem c1464448 : checkChunk 1464448 128 = true := by decide +kernel
private theorem c1464576 : checkChunk 1464576 128 = true := by decide +kernel
private theorem c1464704 : checkChunk 1464704 128 = true := by decide +kernel
private theorem c1464832 : checkChunk 1464832 128 = true := by decide +kernel
private theorem c1464960 : checkChunk 1464960 128 = true := by decide +kernel
private theorem c1465088 : checkChunk 1465088 128 = true := by decide +kernel
private theorem c1465216 : checkChunk 1465216 128 = true := by decide +kernel
private theorem c1465344 : checkChunk 1465344 128 = true := by decide +kernel
private theorem c1465472 : checkChunk 1465472 128 = true := by decide +kernel
private theorem c1465600 : checkChunk 1465600 128 = true := by decide +kernel
private theorem c1465728 : checkChunk 1465728 128 = true := by decide +kernel
private theorem c1465856 : checkChunk 1465856 128 = true := by decide +kernel
private theorem c1465984 : checkChunk 1465984 128 = true := by decide +kernel
private theorem c1466112 : checkChunk 1466112 128 = true := by decide +kernel
private theorem c1466240 : checkChunk 1466240 128 = true := by decide +kernel

public theorem checked : Checked 1458176 1466368 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1458176 128 c1458176) (checkChunk_sound 1458304 128 c1458304)) (Checked.append (checkChunk_sound 1458432 128 c1458432) (checkChunk_sound 1458560 128 c1458560))) (Checked.append (Checked.append (checkChunk_sound 1458688 128 c1458688) (checkChunk_sound 1458816 128 c1458816)) (Checked.append (checkChunk_sound 1458944 128 c1458944) (checkChunk_sound 1459072 128 c1459072)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1459200 128 c1459200) (checkChunk_sound 1459328 128 c1459328)) (Checked.append (checkChunk_sound 1459456 128 c1459456) (checkChunk_sound 1459584 128 c1459584))) (Checked.append (Checked.append (checkChunk_sound 1459712 128 c1459712) (checkChunk_sound 1459840 128 c1459840)) (Checked.append (checkChunk_sound 1459968 128 c1459968) (checkChunk_sound 1460096 128 c1460096))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1460224 128 c1460224) (checkChunk_sound 1460352 128 c1460352)) (Checked.append (checkChunk_sound 1460480 128 c1460480) (checkChunk_sound 1460608 128 c1460608))) (Checked.append (Checked.append (checkChunk_sound 1460736 128 c1460736) (checkChunk_sound 1460864 128 c1460864)) (Checked.append (checkChunk_sound 1460992 128 c1460992) (checkChunk_sound 1461120 128 c1461120)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1461248 128 c1461248) (checkChunk_sound 1461376 128 c1461376)) (Checked.append (checkChunk_sound 1461504 128 c1461504) (checkChunk_sound 1461632 128 c1461632))) (Checked.append (Checked.append (checkChunk_sound 1461760 128 c1461760) (checkChunk_sound 1461888 128 c1461888)) (Checked.append (checkChunk_sound 1462016 128 c1462016) (checkChunk_sound 1462144 128 c1462144)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1462272 128 c1462272) (checkChunk_sound 1462400 128 c1462400)) (Checked.append (checkChunk_sound 1462528 128 c1462528) (checkChunk_sound 1462656 128 c1462656))) (Checked.append (Checked.append (checkChunk_sound 1462784 128 c1462784) (checkChunk_sound 1462912 128 c1462912)) (Checked.append (checkChunk_sound 1463040 128 c1463040) (checkChunk_sound 1463168 128 c1463168)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1463296 128 c1463296) (checkChunk_sound 1463424 128 c1463424)) (Checked.append (checkChunk_sound 1463552 128 c1463552) (checkChunk_sound 1463680 128 c1463680))) (Checked.append (Checked.append (checkChunk_sound 1463808 128 c1463808) (checkChunk_sound 1463936 128 c1463936)) (Checked.append (checkChunk_sound 1464064 128 c1464064) (checkChunk_sound 1464192 128 c1464192))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1464320 128 c1464320) (checkChunk_sound 1464448 128 c1464448)) (Checked.append (checkChunk_sound 1464576 128 c1464576) (checkChunk_sound 1464704 128 c1464704))) (Checked.append (Checked.append (checkChunk_sound 1464832 128 c1464832) (checkChunk_sound 1464960 128 c1464960)) (Checked.append (checkChunk_sound 1465088 128 c1465088) (checkChunk_sound 1465216 128 c1465216)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1465344 128 c1465344) (checkChunk_sound 1465472 128 c1465472)) (Checked.append (checkChunk_sound 1465600 128 c1465600) (checkChunk_sound 1465728 128 c1465728))) (Checked.append (Checked.append (checkChunk_sound 1465856 128 c1465856) (checkChunk_sound 1465984 128 c1465984)) (Checked.append (checkChunk_sound 1466112 128 c1466112) (checkChunk_sound 1466240 128 c1466240)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B021
