module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1548288, 1556480).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B006
private theorem c1548288 : checkChunk 1548288 128 = true := by decide +kernel
private theorem c1548416 : checkChunk 1548416 128 = true := by decide +kernel
private theorem c1548544 : checkChunk 1548544 128 = true := by decide +kernel
private theorem c1548672 : checkChunk 1548672 128 = true := by decide +kernel
private theorem c1548800 : checkChunk 1548800 128 = true := by decide +kernel
private theorem c1548928 : checkChunk 1548928 128 = true := by decide +kernel
private theorem c1549056 : checkChunk 1549056 128 = true := by decide +kernel
private theorem c1549184 : checkChunk 1549184 128 = true := by decide +kernel
private theorem c1549312 : checkChunk 1549312 128 = true := by decide +kernel
private theorem c1549440 : checkChunk 1549440 128 = true := by decide +kernel
private theorem c1549568 : checkChunk 1549568 128 = true := by decide +kernel
private theorem c1549696 : checkChunk 1549696 128 = true := by decide +kernel
private theorem c1549824 : checkChunk 1549824 128 = true := by decide +kernel
private theorem c1549952 : checkChunk 1549952 128 = true := by decide +kernel
private theorem c1550080 : checkChunk 1550080 128 = true := by decide +kernel
private theorem c1550208 : checkChunk 1550208 128 = true := by decide +kernel
private theorem c1550336 : checkChunk 1550336 128 = true := by decide +kernel
private theorem c1550464 : checkChunk 1550464 128 = true := by decide +kernel
private theorem c1550592 : checkChunk 1550592 128 = true := by decide +kernel
private theorem c1550720 : checkChunk 1550720 128 = true := by decide +kernel
private theorem c1550848 : checkChunk 1550848 128 = true := by decide +kernel
private theorem c1550976 : checkChunk 1550976 128 = true := by decide +kernel
private theorem c1551104 : checkChunk 1551104 128 = true := by decide +kernel
private theorem c1551232 : checkChunk 1551232 128 = true := by decide +kernel
private theorem c1551360 : checkChunk 1551360 128 = true := by decide +kernel
private theorem c1551488 : checkChunk 1551488 128 = true := by decide +kernel
private theorem c1551616 : checkChunk 1551616 128 = true := by decide +kernel
private theorem c1551744 : checkChunk 1551744 128 = true := by decide +kernel
private theorem c1551872 : checkChunk 1551872 128 = true := by decide +kernel
private theorem c1552000 : checkChunk 1552000 128 = true := by decide +kernel
private theorem c1552128 : checkChunk 1552128 128 = true := by decide +kernel
private theorem c1552256 : checkChunk 1552256 128 = true := by decide +kernel
private theorem c1552384 : checkChunk 1552384 128 = true := by decide +kernel
private theorem c1552512 : checkChunk 1552512 128 = true := by decide +kernel
private theorem c1552640 : checkChunk 1552640 128 = true := by decide +kernel
private theorem c1552768 : checkChunk 1552768 128 = true := by decide +kernel
private theorem c1552896 : checkChunk 1552896 128 = true := by decide +kernel
private theorem c1553024 : checkChunk 1553024 128 = true := by decide +kernel
private theorem c1553152 : checkChunk 1553152 128 = true := by decide +kernel
private theorem c1553280 : checkChunk 1553280 128 = true := by decide +kernel
private theorem c1553408 : checkChunk 1553408 128 = true := by decide +kernel
private theorem c1553536 : checkChunk 1553536 128 = true := by decide +kernel
private theorem c1553664 : checkChunk 1553664 128 = true := by decide +kernel
private theorem c1553792 : checkChunk 1553792 128 = true := by decide +kernel
private theorem c1553920 : checkChunk 1553920 128 = true := by decide +kernel
private theorem c1554048 : checkChunk 1554048 128 = true := by decide +kernel
private theorem c1554176 : checkChunk 1554176 128 = true := by decide +kernel
private theorem c1554304 : checkChunk 1554304 128 = true := by decide +kernel
private theorem c1554432 : checkChunk 1554432 128 = true := by decide +kernel
private theorem c1554560 : checkChunk 1554560 128 = true := by decide +kernel
private theorem c1554688 : checkChunk 1554688 128 = true := by decide +kernel
private theorem c1554816 : checkChunk 1554816 128 = true := by decide +kernel
private theorem c1554944 : checkChunk 1554944 128 = true := by decide +kernel
private theorem c1555072 : checkChunk 1555072 128 = true := by decide +kernel
private theorem c1555200 : checkChunk 1555200 128 = true := by decide +kernel
private theorem c1555328 : checkChunk 1555328 128 = true := by decide +kernel
private theorem c1555456 : checkChunk 1555456 128 = true := by decide +kernel
private theorem c1555584 : checkChunk 1555584 128 = true := by decide +kernel
private theorem c1555712 : checkChunk 1555712 128 = true := by decide +kernel
private theorem c1555840 : checkChunk 1555840 128 = true := by decide +kernel
private theorem c1555968 : checkChunk 1555968 128 = true := by decide +kernel
private theorem c1556096 : checkChunk 1556096 128 = true := by decide +kernel
private theorem c1556224 : checkChunk 1556224 128 = true := by decide +kernel
private theorem c1556352 : checkChunk 1556352 128 = true := by decide +kernel

public theorem checked : Checked 1548288 1556480 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1548288 128 c1548288) (checkChunk_sound 1548416 128 c1548416)) (Checked.append (checkChunk_sound 1548544 128 c1548544) (checkChunk_sound 1548672 128 c1548672))) (Checked.append (Checked.append (checkChunk_sound 1548800 128 c1548800) (checkChunk_sound 1548928 128 c1548928)) (Checked.append (checkChunk_sound 1549056 128 c1549056) (checkChunk_sound 1549184 128 c1549184)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1549312 128 c1549312) (checkChunk_sound 1549440 128 c1549440)) (Checked.append (checkChunk_sound 1549568 128 c1549568) (checkChunk_sound 1549696 128 c1549696))) (Checked.append (Checked.append (checkChunk_sound 1549824 128 c1549824) (checkChunk_sound 1549952 128 c1549952)) (Checked.append (checkChunk_sound 1550080 128 c1550080) (checkChunk_sound 1550208 128 c1550208))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1550336 128 c1550336) (checkChunk_sound 1550464 128 c1550464)) (Checked.append (checkChunk_sound 1550592 128 c1550592) (checkChunk_sound 1550720 128 c1550720))) (Checked.append (Checked.append (checkChunk_sound 1550848 128 c1550848) (checkChunk_sound 1550976 128 c1550976)) (Checked.append (checkChunk_sound 1551104 128 c1551104) (checkChunk_sound 1551232 128 c1551232)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1551360 128 c1551360) (checkChunk_sound 1551488 128 c1551488)) (Checked.append (checkChunk_sound 1551616 128 c1551616) (checkChunk_sound 1551744 128 c1551744))) (Checked.append (Checked.append (checkChunk_sound 1551872 128 c1551872) (checkChunk_sound 1552000 128 c1552000)) (Checked.append (checkChunk_sound 1552128 128 c1552128) (checkChunk_sound 1552256 128 c1552256)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1552384 128 c1552384) (checkChunk_sound 1552512 128 c1552512)) (Checked.append (checkChunk_sound 1552640 128 c1552640) (checkChunk_sound 1552768 128 c1552768))) (Checked.append (Checked.append (checkChunk_sound 1552896 128 c1552896) (checkChunk_sound 1553024 128 c1553024)) (Checked.append (checkChunk_sound 1553152 128 c1553152) (checkChunk_sound 1553280 128 c1553280)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1553408 128 c1553408) (checkChunk_sound 1553536 128 c1553536)) (Checked.append (checkChunk_sound 1553664 128 c1553664) (checkChunk_sound 1553792 128 c1553792))) (Checked.append (Checked.append (checkChunk_sound 1553920 128 c1553920) (checkChunk_sound 1554048 128 c1554048)) (Checked.append (checkChunk_sound 1554176 128 c1554176) (checkChunk_sound 1554304 128 c1554304))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1554432 128 c1554432) (checkChunk_sound 1554560 128 c1554560)) (Checked.append (checkChunk_sound 1554688 128 c1554688) (checkChunk_sound 1554816 128 c1554816))) (Checked.append (Checked.append (checkChunk_sound 1554944 128 c1554944) (checkChunk_sound 1555072 128 c1555072)) (Checked.append (checkChunk_sound 1555200 128 c1555200) (checkChunk_sound 1555328 128 c1555328)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1555456 128 c1555456) (checkChunk_sound 1555584 128 c1555584)) (Checked.append (checkChunk_sound 1555712 128 c1555712) (checkChunk_sound 1555840 128 c1555840))) (Checked.append (Checked.append (checkChunk_sound 1555968 128 c1555968) (checkChunk_sound 1556096 128 c1556096)) (Checked.append (checkChunk_sound 1556224 128 c1556224) (checkChunk_sound 1556352 128 c1556352)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B006
