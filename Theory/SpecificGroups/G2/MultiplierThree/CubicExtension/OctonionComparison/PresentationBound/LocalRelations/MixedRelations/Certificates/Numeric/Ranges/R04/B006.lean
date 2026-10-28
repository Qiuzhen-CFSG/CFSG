module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [909312, 917504).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B006
private theorem c909312 : checkChunk 909312 128 = true := by decide +kernel
private theorem c909440 : checkChunk 909440 128 = true := by decide +kernel
private theorem c909568 : checkChunk 909568 128 = true := by decide +kernel
private theorem c909696 : checkChunk 909696 128 = true := by decide +kernel
private theorem c909824 : checkChunk 909824 128 = true := by decide +kernel
private theorem c909952 : checkChunk 909952 128 = true := by decide +kernel
private theorem c910080 : checkChunk 910080 128 = true := by decide +kernel
private theorem c910208 : checkChunk 910208 128 = true := by decide +kernel
private theorem c910336 : checkChunk 910336 128 = true := by decide +kernel
private theorem c910464 : checkChunk 910464 128 = true := by decide +kernel
private theorem c910592 : checkChunk 910592 128 = true := by decide +kernel
private theorem c910720 : checkChunk 910720 128 = true := by decide +kernel
private theorem c910848 : checkChunk 910848 128 = true := by decide +kernel
private theorem c910976 : checkChunk 910976 128 = true := by decide +kernel
private theorem c911104 : checkChunk 911104 128 = true := by decide +kernel
private theorem c911232 : checkChunk 911232 128 = true := by decide +kernel
private theorem c911360 : checkChunk 911360 128 = true := by decide +kernel
private theorem c911488 : checkChunk 911488 128 = true := by decide +kernel
private theorem c911616 : checkChunk 911616 128 = true := by decide +kernel
private theorem c911744 : checkChunk 911744 128 = true := by decide +kernel
private theorem c911872 : checkChunk 911872 128 = true := by decide +kernel
private theorem c912000 : checkChunk 912000 128 = true := by decide +kernel
private theorem c912128 : checkChunk 912128 128 = true := by decide +kernel
private theorem c912256 : checkChunk 912256 128 = true := by decide +kernel
private theorem c912384 : checkChunk 912384 128 = true := by decide +kernel
private theorem c912512 : checkChunk 912512 128 = true := by decide +kernel
private theorem c912640 : checkChunk 912640 128 = true := by decide +kernel
private theorem c912768 : checkChunk 912768 128 = true := by decide +kernel
private theorem c912896 : checkChunk 912896 128 = true := by decide +kernel
private theorem c913024 : checkChunk 913024 128 = true := by decide +kernel
private theorem c913152 : checkChunk 913152 128 = true := by decide +kernel
private theorem c913280 : checkChunk 913280 128 = true := by decide +kernel
private theorem c913408 : checkChunk 913408 128 = true := by decide +kernel
private theorem c913536 : checkChunk 913536 128 = true := by decide +kernel
private theorem c913664 : checkChunk 913664 128 = true := by decide +kernel
private theorem c913792 : checkChunk 913792 128 = true := by decide +kernel
private theorem c913920 : checkChunk 913920 128 = true := by decide +kernel
private theorem c914048 : checkChunk 914048 128 = true := by decide +kernel
private theorem c914176 : checkChunk 914176 128 = true := by decide +kernel
private theorem c914304 : checkChunk 914304 128 = true := by decide +kernel
private theorem c914432 : checkChunk 914432 128 = true := by decide +kernel
private theorem c914560 : checkChunk 914560 128 = true := by decide +kernel
private theorem c914688 : checkChunk 914688 128 = true := by decide +kernel
private theorem c914816 : checkChunk 914816 128 = true := by decide +kernel
private theorem c914944 : checkChunk 914944 128 = true := by decide +kernel
private theorem c915072 : checkChunk 915072 128 = true := by decide +kernel
private theorem c915200 : checkChunk 915200 128 = true := by decide +kernel
private theorem c915328 : checkChunk 915328 128 = true := by decide +kernel
private theorem c915456 : checkChunk 915456 128 = true := by decide +kernel
private theorem c915584 : checkChunk 915584 128 = true := by decide +kernel
private theorem c915712 : checkChunk 915712 128 = true := by decide +kernel
private theorem c915840 : checkChunk 915840 128 = true := by decide +kernel
private theorem c915968 : checkChunk 915968 128 = true := by decide +kernel
private theorem c916096 : checkChunk 916096 128 = true := by decide +kernel
private theorem c916224 : checkChunk 916224 128 = true := by decide +kernel
private theorem c916352 : checkChunk 916352 128 = true := by decide +kernel
private theorem c916480 : checkChunk 916480 128 = true := by decide +kernel
private theorem c916608 : checkChunk 916608 128 = true := by decide +kernel
private theorem c916736 : checkChunk 916736 128 = true := by decide +kernel
private theorem c916864 : checkChunk 916864 128 = true := by decide +kernel
private theorem c916992 : checkChunk 916992 128 = true := by decide +kernel
private theorem c917120 : checkChunk 917120 128 = true := by decide +kernel
private theorem c917248 : checkChunk 917248 128 = true := by decide +kernel
private theorem c917376 : checkChunk 917376 128 = true := by decide +kernel

public theorem checked : Checked 909312 917504 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 909312 128 c909312) (checkChunk_sound 909440 128 c909440)) (Checked.append (checkChunk_sound 909568 128 c909568) (checkChunk_sound 909696 128 c909696))) (Checked.append (Checked.append (checkChunk_sound 909824 128 c909824) (checkChunk_sound 909952 128 c909952)) (Checked.append (checkChunk_sound 910080 128 c910080) (checkChunk_sound 910208 128 c910208)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 910336 128 c910336) (checkChunk_sound 910464 128 c910464)) (Checked.append (checkChunk_sound 910592 128 c910592) (checkChunk_sound 910720 128 c910720))) (Checked.append (Checked.append (checkChunk_sound 910848 128 c910848) (checkChunk_sound 910976 128 c910976)) (Checked.append (checkChunk_sound 911104 128 c911104) (checkChunk_sound 911232 128 c911232))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 911360 128 c911360) (checkChunk_sound 911488 128 c911488)) (Checked.append (checkChunk_sound 911616 128 c911616) (checkChunk_sound 911744 128 c911744))) (Checked.append (Checked.append (checkChunk_sound 911872 128 c911872) (checkChunk_sound 912000 128 c912000)) (Checked.append (checkChunk_sound 912128 128 c912128) (checkChunk_sound 912256 128 c912256)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 912384 128 c912384) (checkChunk_sound 912512 128 c912512)) (Checked.append (checkChunk_sound 912640 128 c912640) (checkChunk_sound 912768 128 c912768))) (Checked.append (Checked.append (checkChunk_sound 912896 128 c912896) (checkChunk_sound 913024 128 c913024)) (Checked.append (checkChunk_sound 913152 128 c913152) (checkChunk_sound 913280 128 c913280)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 913408 128 c913408) (checkChunk_sound 913536 128 c913536)) (Checked.append (checkChunk_sound 913664 128 c913664) (checkChunk_sound 913792 128 c913792))) (Checked.append (Checked.append (checkChunk_sound 913920 128 c913920) (checkChunk_sound 914048 128 c914048)) (Checked.append (checkChunk_sound 914176 128 c914176) (checkChunk_sound 914304 128 c914304)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 914432 128 c914432) (checkChunk_sound 914560 128 c914560)) (Checked.append (checkChunk_sound 914688 128 c914688) (checkChunk_sound 914816 128 c914816))) (Checked.append (Checked.append (checkChunk_sound 914944 128 c914944) (checkChunk_sound 915072 128 c915072)) (Checked.append (checkChunk_sound 915200 128 c915200) (checkChunk_sound 915328 128 c915328))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 915456 128 c915456) (checkChunk_sound 915584 128 c915584)) (Checked.append (checkChunk_sound 915712 128 c915712) (checkChunk_sound 915840 128 c915840))) (Checked.append (Checked.append (checkChunk_sound 915968 128 c915968) (checkChunk_sound 916096 128 c916096)) (Checked.append (checkChunk_sound 916224 128 c916224) (checkChunk_sound 916352 128 c916352)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 916480 128 c916480) (checkChunk_sound 916608 128 c916608)) (Checked.append (checkChunk_sound 916736 128 c916736) (checkChunk_sound 916864 128 c916864))) (Checked.append (Checked.append (checkChunk_sound 916992 128 c916992) (checkChunk_sound 917120 128 c917120)) (Checked.append (checkChunk_sound 917248 128 c917248) (checkChunk_sound 917376 128 c917376)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B006
