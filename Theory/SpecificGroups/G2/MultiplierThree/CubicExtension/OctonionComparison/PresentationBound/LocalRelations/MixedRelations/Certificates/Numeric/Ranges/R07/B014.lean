module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1613824, 1622016).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B014
private theorem c1613824 : checkChunk 1613824 128 = true := by decide +kernel
private theorem c1613952 : checkChunk 1613952 128 = true := by decide +kernel
private theorem c1614080 : checkChunk 1614080 128 = true := by decide +kernel
private theorem c1614208 : checkChunk 1614208 128 = true := by decide +kernel
private theorem c1614336 : checkChunk 1614336 128 = true := by decide +kernel
private theorem c1614464 : checkChunk 1614464 128 = true := by decide +kernel
private theorem c1614592 : checkChunk 1614592 128 = true := by decide +kernel
private theorem c1614720 : checkChunk 1614720 128 = true := by decide +kernel
private theorem c1614848 : checkChunk 1614848 128 = true := by decide +kernel
private theorem c1614976 : checkChunk 1614976 128 = true := by decide +kernel
private theorem c1615104 : checkChunk 1615104 128 = true := by decide +kernel
private theorem c1615232 : checkChunk 1615232 128 = true := by decide +kernel
private theorem c1615360 : checkChunk 1615360 128 = true := by decide +kernel
private theorem c1615488 : checkChunk 1615488 128 = true := by decide +kernel
private theorem c1615616 : checkChunk 1615616 128 = true := by decide +kernel
private theorem c1615744 : checkChunk 1615744 128 = true := by decide +kernel
private theorem c1615872 : checkChunk 1615872 128 = true := by decide +kernel
private theorem c1616000 : checkChunk 1616000 128 = true := by decide +kernel
private theorem c1616128 : checkChunk 1616128 128 = true := by decide +kernel
private theorem c1616256 : checkChunk 1616256 128 = true := by decide +kernel
private theorem c1616384 : checkChunk 1616384 128 = true := by decide +kernel
private theorem c1616512 : checkChunk 1616512 128 = true := by decide +kernel
private theorem c1616640 : checkChunk 1616640 128 = true := by decide +kernel
private theorem c1616768 : checkChunk 1616768 128 = true := by decide +kernel
private theorem c1616896 : checkChunk 1616896 128 = true := by decide +kernel
private theorem c1617024 : checkChunk 1617024 128 = true := by decide +kernel
private theorem c1617152 : checkChunk 1617152 128 = true := by decide +kernel
private theorem c1617280 : checkChunk 1617280 128 = true := by decide +kernel
private theorem c1617408 : checkChunk 1617408 128 = true := by decide +kernel
private theorem c1617536 : checkChunk 1617536 128 = true := by decide +kernel
private theorem c1617664 : checkChunk 1617664 128 = true := by decide +kernel
private theorem c1617792 : checkChunk 1617792 128 = true := by decide +kernel
private theorem c1617920 : checkChunk 1617920 128 = true := by decide +kernel
private theorem c1618048 : checkChunk 1618048 128 = true := by decide +kernel
private theorem c1618176 : checkChunk 1618176 128 = true := by decide +kernel
private theorem c1618304 : checkChunk 1618304 128 = true := by decide +kernel
private theorem c1618432 : checkChunk 1618432 128 = true := by decide +kernel
private theorem c1618560 : checkChunk 1618560 128 = true := by decide +kernel
private theorem c1618688 : checkChunk 1618688 128 = true := by decide +kernel
private theorem c1618816 : checkChunk 1618816 128 = true := by decide +kernel
private theorem c1618944 : checkChunk 1618944 128 = true := by decide +kernel
private theorem c1619072 : checkChunk 1619072 128 = true := by decide +kernel
private theorem c1619200 : checkChunk 1619200 128 = true := by decide +kernel
private theorem c1619328 : checkChunk 1619328 128 = true := by decide +kernel
private theorem c1619456 : checkChunk 1619456 128 = true := by decide +kernel
private theorem c1619584 : checkChunk 1619584 128 = true := by decide +kernel
private theorem c1619712 : checkChunk 1619712 128 = true := by decide +kernel
private theorem c1619840 : checkChunk 1619840 128 = true := by decide +kernel
private theorem c1619968 : checkChunk 1619968 128 = true := by decide +kernel
private theorem c1620096 : checkChunk 1620096 128 = true := by decide +kernel
private theorem c1620224 : checkChunk 1620224 128 = true := by decide +kernel
private theorem c1620352 : checkChunk 1620352 128 = true := by decide +kernel
private theorem c1620480 : checkChunk 1620480 128 = true := by decide +kernel
private theorem c1620608 : checkChunk 1620608 128 = true := by decide +kernel
private theorem c1620736 : checkChunk 1620736 128 = true := by decide +kernel
private theorem c1620864 : checkChunk 1620864 128 = true := by decide +kernel
private theorem c1620992 : checkChunk 1620992 128 = true := by decide +kernel
private theorem c1621120 : checkChunk 1621120 128 = true := by decide +kernel
private theorem c1621248 : checkChunk 1621248 128 = true := by decide +kernel
private theorem c1621376 : checkChunk 1621376 128 = true := by decide +kernel
private theorem c1621504 : checkChunk 1621504 128 = true := by decide +kernel
private theorem c1621632 : checkChunk 1621632 128 = true := by decide +kernel
private theorem c1621760 : checkChunk 1621760 128 = true := by decide +kernel
private theorem c1621888 : checkChunk 1621888 128 = true := by decide +kernel

public theorem checked : Checked 1613824 1622016 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1613824 128 c1613824) (checkChunk_sound 1613952 128 c1613952)) (Checked.append (checkChunk_sound 1614080 128 c1614080) (checkChunk_sound 1614208 128 c1614208))) (Checked.append (Checked.append (checkChunk_sound 1614336 128 c1614336) (checkChunk_sound 1614464 128 c1614464)) (Checked.append (checkChunk_sound 1614592 128 c1614592) (checkChunk_sound 1614720 128 c1614720)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1614848 128 c1614848) (checkChunk_sound 1614976 128 c1614976)) (Checked.append (checkChunk_sound 1615104 128 c1615104) (checkChunk_sound 1615232 128 c1615232))) (Checked.append (Checked.append (checkChunk_sound 1615360 128 c1615360) (checkChunk_sound 1615488 128 c1615488)) (Checked.append (checkChunk_sound 1615616 128 c1615616) (checkChunk_sound 1615744 128 c1615744))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1615872 128 c1615872) (checkChunk_sound 1616000 128 c1616000)) (Checked.append (checkChunk_sound 1616128 128 c1616128) (checkChunk_sound 1616256 128 c1616256))) (Checked.append (Checked.append (checkChunk_sound 1616384 128 c1616384) (checkChunk_sound 1616512 128 c1616512)) (Checked.append (checkChunk_sound 1616640 128 c1616640) (checkChunk_sound 1616768 128 c1616768)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1616896 128 c1616896) (checkChunk_sound 1617024 128 c1617024)) (Checked.append (checkChunk_sound 1617152 128 c1617152) (checkChunk_sound 1617280 128 c1617280))) (Checked.append (Checked.append (checkChunk_sound 1617408 128 c1617408) (checkChunk_sound 1617536 128 c1617536)) (Checked.append (checkChunk_sound 1617664 128 c1617664) (checkChunk_sound 1617792 128 c1617792)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1617920 128 c1617920) (checkChunk_sound 1618048 128 c1618048)) (Checked.append (checkChunk_sound 1618176 128 c1618176) (checkChunk_sound 1618304 128 c1618304))) (Checked.append (Checked.append (checkChunk_sound 1618432 128 c1618432) (checkChunk_sound 1618560 128 c1618560)) (Checked.append (checkChunk_sound 1618688 128 c1618688) (checkChunk_sound 1618816 128 c1618816)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1618944 128 c1618944) (checkChunk_sound 1619072 128 c1619072)) (Checked.append (checkChunk_sound 1619200 128 c1619200) (checkChunk_sound 1619328 128 c1619328))) (Checked.append (Checked.append (checkChunk_sound 1619456 128 c1619456) (checkChunk_sound 1619584 128 c1619584)) (Checked.append (checkChunk_sound 1619712 128 c1619712) (checkChunk_sound 1619840 128 c1619840))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1619968 128 c1619968) (checkChunk_sound 1620096 128 c1620096)) (Checked.append (checkChunk_sound 1620224 128 c1620224) (checkChunk_sound 1620352 128 c1620352))) (Checked.append (Checked.append (checkChunk_sound 1620480 128 c1620480) (checkChunk_sound 1620608 128 c1620608)) (Checked.append (checkChunk_sound 1620736 128 c1620736) (checkChunk_sound 1620864 128 c1620864)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1620992 128 c1620992) (checkChunk_sound 1621120 128 c1621120)) (Checked.append (checkChunk_sound 1621248 128 c1621248) (checkChunk_sound 1621376 128 c1621376))) (Checked.append (Checked.append (checkChunk_sound 1621504 128 c1621504) (checkChunk_sound 1621632 128 c1621632)) (Checked.append (checkChunk_sound 1621760 128 c1621760) (checkChunk_sound 1621888 128 c1621888)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B014
