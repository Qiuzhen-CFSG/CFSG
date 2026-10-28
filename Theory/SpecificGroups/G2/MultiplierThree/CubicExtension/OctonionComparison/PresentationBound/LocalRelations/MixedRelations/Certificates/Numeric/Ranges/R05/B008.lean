module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1138688, 1146880).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B008
private theorem c1138688 : checkChunk 1138688 128 = true := by decide +kernel
private theorem c1138816 : checkChunk 1138816 128 = true := by decide +kernel
private theorem c1138944 : checkChunk 1138944 128 = true := by decide +kernel
private theorem c1139072 : checkChunk 1139072 128 = true := by decide +kernel
private theorem c1139200 : checkChunk 1139200 128 = true := by decide +kernel
private theorem c1139328 : checkChunk 1139328 128 = true := by decide +kernel
private theorem c1139456 : checkChunk 1139456 128 = true := by decide +kernel
private theorem c1139584 : checkChunk 1139584 128 = true := by decide +kernel
private theorem c1139712 : checkChunk 1139712 128 = true := by decide +kernel
private theorem c1139840 : checkChunk 1139840 128 = true := by decide +kernel
private theorem c1139968 : checkChunk 1139968 128 = true := by decide +kernel
private theorem c1140096 : checkChunk 1140096 128 = true := by decide +kernel
private theorem c1140224 : checkChunk 1140224 128 = true := by decide +kernel
private theorem c1140352 : checkChunk 1140352 128 = true := by decide +kernel
private theorem c1140480 : checkChunk 1140480 128 = true := by decide +kernel
private theorem c1140608 : checkChunk 1140608 128 = true := by decide +kernel
private theorem c1140736 : checkChunk 1140736 128 = true := by decide +kernel
private theorem c1140864 : checkChunk 1140864 128 = true := by decide +kernel
private theorem c1140992 : checkChunk 1140992 128 = true := by decide +kernel
private theorem c1141120 : checkChunk 1141120 128 = true := by decide +kernel
private theorem c1141248 : checkChunk 1141248 128 = true := by decide +kernel
private theorem c1141376 : checkChunk 1141376 128 = true := by decide +kernel
private theorem c1141504 : checkChunk 1141504 128 = true := by decide +kernel
private theorem c1141632 : checkChunk 1141632 128 = true := by decide +kernel
private theorem c1141760 : checkChunk 1141760 128 = true := by decide +kernel
private theorem c1141888 : checkChunk 1141888 128 = true := by decide +kernel
private theorem c1142016 : checkChunk 1142016 128 = true := by decide +kernel
private theorem c1142144 : checkChunk 1142144 128 = true := by decide +kernel
private theorem c1142272 : checkChunk 1142272 128 = true := by decide +kernel
private theorem c1142400 : checkChunk 1142400 128 = true := by decide +kernel
private theorem c1142528 : checkChunk 1142528 128 = true := by decide +kernel
private theorem c1142656 : checkChunk 1142656 128 = true := by decide +kernel
private theorem c1142784 : checkChunk 1142784 128 = true := by decide +kernel
private theorem c1142912 : checkChunk 1142912 128 = true := by decide +kernel
private theorem c1143040 : checkChunk 1143040 128 = true := by decide +kernel
private theorem c1143168 : checkChunk 1143168 128 = true := by decide +kernel
private theorem c1143296 : checkChunk 1143296 128 = true := by decide +kernel
private theorem c1143424 : checkChunk 1143424 128 = true := by decide +kernel
private theorem c1143552 : checkChunk 1143552 128 = true := by decide +kernel
private theorem c1143680 : checkChunk 1143680 128 = true := by decide +kernel
private theorem c1143808 : checkChunk 1143808 128 = true := by decide +kernel
private theorem c1143936 : checkChunk 1143936 128 = true := by decide +kernel
private theorem c1144064 : checkChunk 1144064 128 = true := by decide +kernel
private theorem c1144192 : checkChunk 1144192 128 = true := by decide +kernel
private theorem c1144320 : checkChunk 1144320 128 = true := by decide +kernel
private theorem c1144448 : checkChunk 1144448 128 = true := by decide +kernel
private theorem c1144576 : checkChunk 1144576 128 = true := by decide +kernel
private theorem c1144704 : checkChunk 1144704 128 = true := by decide +kernel
private theorem c1144832 : checkChunk 1144832 128 = true := by decide +kernel
private theorem c1144960 : checkChunk 1144960 128 = true := by decide +kernel
private theorem c1145088 : checkChunk 1145088 128 = true := by decide +kernel
private theorem c1145216 : checkChunk 1145216 128 = true := by decide +kernel
private theorem c1145344 : checkChunk 1145344 128 = true := by decide +kernel
private theorem c1145472 : checkChunk 1145472 128 = true := by decide +kernel
private theorem c1145600 : checkChunk 1145600 128 = true := by decide +kernel
private theorem c1145728 : checkChunk 1145728 128 = true := by decide +kernel
private theorem c1145856 : checkChunk 1145856 128 = true := by decide +kernel
private theorem c1145984 : checkChunk 1145984 128 = true := by decide +kernel
private theorem c1146112 : checkChunk 1146112 128 = true := by decide +kernel
private theorem c1146240 : checkChunk 1146240 128 = true := by decide +kernel
private theorem c1146368 : checkChunk 1146368 128 = true := by decide +kernel
private theorem c1146496 : checkChunk 1146496 128 = true := by decide +kernel
private theorem c1146624 : checkChunk 1146624 128 = true := by decide +kernel
private theorem c1146752 : checkChunk 1146752 128 = true := by decide +kernel

public theorem checked : Checked 1138688 1146880 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1138688 128 c1138688) (checkChunk_sound 1138816 128 c1138816)) (Checked.append (checkChunk_sound 1138944 128 c1138944) (checkChunk_sound 1139072 128 c1139072))) (Checked.append (Checked.append (checkChunk_sound 1139200 128 c1139200) (checkChunk_sound 1139328 128 c1139328)) (Checked.append (checkChunk_sound 1139456 128 c1139456) (checkChunk_sound 1139584 128 c1139584)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1139712 128 c1139712) (checkChunk_sound 1139840 128 c1139840)) (Checked.append (checkChunk_sound 1139968 128 c1139968) (checkChunk_sound 1140096 128 c1140096))) (Checked.append (Checked.append (checkChunk_sound 1140224 128 c1140224) (checkChunk_sound 1140352 128 c1140352)) (Checked.append (checkChunk_sound 1140480 128 c1140480) (checkChunk_sound 1140608 128 c1140608))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1140736 128 c1140736) (checkChunk_sound 1140864 128 c1140864)) (Checked.append (checkChunk_sound 1140992 128 c1140992) (checkChunk_sound 1141120 128 c1141120))) (Checked.append (Checked.append (checkChunk_sound 1141248 128 c1141248) (checkChunk_sound 1141376 128 c1141376)) (Checked.append (checkChunk_sound 1141504 128 c1141504) (checkChunk_sound 1141632 128 c1141632)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1141760 128 c1141760) (checkChunk_sound 1141888 128 c1141888)) (Checked.append (checkChunk_sound 1142016 128 c1142016) (checkChunk_sound 1142144 128 c1142144))) (Checked.append (Checked.append (checkChunk_sound 1142272 128 c1142272) (checkChunk_sound 1142400 128 c1142400)) (Checked.append (checkChunk_sound 1142528 128 c1142528) (checkChunk_sound 1142656 128 c1142656)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1142784 128 c1142784) (checkChunk_sound 1142912 128 c1142912)) (Checked.append (checkChunk_sound 1143040 128 c1143040) (checkChunk_sound 1143168 128 c1143168))) (Checked.append (Checked.append (checkChunk_sound 1143296 128 c1143296) (checkChunk_sound 1143424 128 c1143424)) (Checked.append (checkChunk_sound 1143552 128 c1143552) (checkChunk_sound 1143680 128 c1143680)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1143808 128 c1143808) (checkChunk_sound 1143936 128 c1143936)) (Checked.append (checkChunk_sound 1144064 128 c1144064) (checkChunk_sound 1144192 128 c1144192))) (Checked.append (Checked.append (checkChunk_sound 1144320 128 c1144320) (checkChunk_sound 1144448 128 c1144448)) (Checked.append (checkChunk_sound 1144576 128 c1144576) (checkChunk_sound 1144704 128 c1144704))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1144832 128 c1144832) (checkChunk_sound 1144960 128 c1144960)) (Checked.append (checkChunk_sound 1145088 128 c1145088) (checkChunk_sound 1145216 128 c1145216))) (Checked.append (Checked.append (checkChunk_sound 1145344 128 c1145344) (checkChunk_sound 1145472 128 c1145472)) (Checked.append (checkChunk_sound 1145600 128 c1145600) (checkChunk_sound 1145728 128 c1145728)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1145856 128 c1145856) (checkChunk_sound 1145984 128 c1145984)) (Checked.append (checkChunk_sound 1146112 128 c1146112) (checkChunk_sound 1146240 128 c1146240))) (Checked.append (Checked.append (checkChunk_sound 1146368 128 c1146368) (checkChunk_sound 1146496 128 c1146496)) (Checked.append (checkChunk_sound 1146624 128 c1146624) (checkChunk_sound 1146752 128 c1146752)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B008
