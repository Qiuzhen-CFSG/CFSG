module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1073152, 1081344).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B000
private theorem c1073152 : checkChunk 1073152 128 = true := by decide +kernel
private theorem c1073280 : checkChunk 1073280 128 = true := by decide +kernel
private theorem c1073408 : checkChunk 1073408 128 = true := by decide +kernel
private theorem c1073536 : checkChunk 1073536 128 = true := by decide +kernel
private theorem c1073664 : checkChunk 1073664 128 = true := by decide +kernel
private theorem c1073792 : checkChunk 1073792 128 = true := by decide +kernel
private theorem c1073920 : checkChunk 1073920 128 = true := by decide +kernel
private theorem c1074048 : checkChunk 1074048 128 = true := by decide +kernel
private theorem c1074176 : checkChunk 1074176 128 = true := by decide +kernel
private theorem c1074304 : checkChunk 1074304 128 = true := by decide +kernel
private theorem c1074432 : checkChunk 1074432 128 = true := by decide +kernel
private theorem c1074560 : checkChunk 1074560 128 = true := by decide +kernel
private theorem c1074688 : checkChunk 1074688 128 = true := by decide +kernel
private theorem c1074816 : checkChunk 1074816 128 = true := by decide +kernel
private theorem c1074944 : checkChunk 1074944 128 = true := by decide +kernel
private theorem c1075072 : checkChunk 1075072 128 = true := by decide +kernel
private theorem c1075200 : checkChunk 1075200 128 = true := by decide +kernel
private theorem c1075328 : checkChunk 1075328 128 = true := by decide +kernel
private theorem c1075456 : checkChunk 1075456 128 = true := by decide +kernel
private theorem c1075584 : checkChunk 1075584 128 = true := by decide +kernel
private theorem c1075712 : checkChunk 1075712 128 = true := by decide +kernel
private theorem c1075840 : checkChunk 1075840 128 = true := by decide +kernel
private theorem c1075968 : checkChunk 1075968 128 = true := by decide +kernel
private theorem c1076096 : checkChunk 1076096 128 = true := by decide +kernel
private theorem c1076224 : checkChunk 1076224 128 = true := by decide +kernel
private theorem c1076352 : checkChunk 1076352 128 = true := by decide +kernel
private theorem c1076480 : checkChunk 1076480 128 = true := by decide +kernel
private theorem c1076608 : checkChunk 1076608 128 = true := by decide +kernel
private theorem c1076736 : checkChunk 1076736 128 = true := by decide +kernel
private theorem c1076864 : checkChunk 1076864 128 = true := by decide +kernel
private theorem c1076992 : checkChunk 1076992 128 = true := by decide +kernel
private theorem c1077120 : checkChunk 1077120 128 = true := by decide +kernel
private theorem c1077248 : checkChunk 1077248 128 = true := by decide +kernel
private theorem c1077376 : checkChunk 1077376 128 = true := by decide +kernel
private theorem c1077504 : checkChunk 1077504 128 = true := by decide +kernel
private theorem c1077632 : checkChunk 1077632 128 = true := by decide +kernel
private theorem c1077760 : checkChunk 1077760 128 = true := by decide +kernel
private theorem c1077888 : checkChunk 1077888 128 = true := by decide +kernel
private theorem c1078016 : checkChunk 1078016 128 = true := by decide +kernel
private theorem c1078144 : checkChunk 1078144 128 = true := by decide +kernel
private theorem c1078272 : checkChunk 1078272 128 = true := by decide +kernel
private theorem c1078400 : checkChunk 1078400 128 = true := by decide +kernel
private theorem c1078528 : checkChunk 1078528 128 = true := by decide +kernel
private theorem c1078656 : checkChunk 1078656 128 = true := by decide +kernel
private theorem c1078784 : checkChunk 1078784 128 = true := by decide +kernel
private theorem c1078912 : checkChunk 1078912 128 = true := by decide +kernel
private theorem c1079040 : checkChunk 1079040 128 = true := by decide +kernel
private theorem c1079168 : checkChunk 1079168 128 = true := by decide +kernel
private theorem c1079296 : checkChunk 1079296 128 = true := by decide +kernel
private theorem c1079424 : checkChunk 1079424 128 = true := by decide +kernel
private theorem c1079552 : checkChunk 1079552 128 = true := by decide +kernel
private theorem c1079680 : checkChunk 1079680 128 = true := by decide +kernel
private theorem c1079808 : checkChunk 1079808 128 = true := by decide +kernel
private theorem c1079936 : checkChunk 1079936 128 = true := by decide +kernel
private theorem c1080064 : checkChunk 1080064 128 = true := by decide +kernel
private theorem c1080192 : checkChunk 1080192 128 = true := by decide +kernel
private theorem c1080320 : checkChunk 1080320 128 = true := by decide +kernel
private theorem c1080448 : checkChunk 1080448 128 = true := by decide +kernel
private theorem c1080576 : checkChunk 1080576 128 = true := by decide +kernel
private theorem c1080704 : checkChunk 1080704 128 = true := by decide +kernel
private theorem c1080832 : checkChunk 1080832 128 = true := by decide +kernel
private theorem c1080960 : checkChunk 1080960 128 = true := by decide +kernel
private theorem c1081088 : checkChunk 1081088 128 = true := by decide +kernel
private theorem c1081216 : checkChunk 1081216 128 = true := by decide +kernel

public theorem checked : Checked 1073152 1081344 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1073152 128 c1073152) (checkChunk_sound 1073280 128 c1073280)) (Checked.append (checkChunk_sound 1073408 128 c1073408) (checkChunk_sound 1073536 128 c1073536))) (Checked.append (Checked.append (checkChunk_sound 1073664 128 c1073664) (checkChunk_sound 1073792 128 c1073792)) (Checked.append (checkChunk_sound 1073920 128 c1073920) (checkChunk_sound 1074048 128 c1074048)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1074176 128 c1074176) (checkChunk_sound 1074304 128 c1074304)) (Checked.append (checkChunk_sound 1074432 128 c1074432) (checkChunk_sound 1074560 128 c1074560))) (Checked.append (Checked.append (checkChunk_sound 1074688 128 c1074688) (checkChunk_sound 1074816 128 c1074816)) (Checked.append (checkChunk_sound 1074944 128 c1074944) (checkChunk_sound 1075072 128 c1075072))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1075200 128 c1075200) (checkChunk_sound 1075328 128 c1075328)) (Checked.append (checkChunk_sound 1075456 128 c1075456) (checkChunk_sound 1075584 128 c1075584))) (Checked.append (Checked.append (checkChunk_sound 1075712 128 c1075712) (checkChunk_sound 1075840 128 c1075840)) (Checked.append (checkChunk_sound 1075968 128 c1075968) (checkChunk_sound 1076096 128 c1076096)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1076224 128 c1076224) (checkChunk_sound 1076352 128 c1076352)) (Checked.append (checkChunk_sound 1076480 128 c1076480) (checkChunk_sound 1076608 128 c1076608))) (Checked.append (Checked.append (checkChunk_sound 1076736 128 c1076736) (checkChunk_sound 1076864 128 c1076864)) (Checked.append (checkChunk_sound 1076992 128 c1076992) (checkChunk_sound 1077120 128 c1077120)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1077248 128 c1077248) (checkChunk_sound 1077376 128 c1077376)) (Checked.append (checkChunk_sound 1077504 128 c1077504) (checkChunk_sound 1077632 128 c1077632))) (Checked.append (Checked.append (checkChunk_sound 1077760 128 c1077760) (checkChunk_sound 1077888 128 c1077888)) (Checked.append (checkChunk_sound 1078016 128 c1078016) (checkChunk_sound 1078144 128 c1078144)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1078272 128 c1078272) (checkChunk_sound 1078400 128 c1078400)) (Checked.append (checkChunk_sound 1078528 128 c1078528) (checkChunk_sound 1078656 128 c1078656))) (Checked.append (Checked.append (checkChunk_sound 1078784 128 c1078784) (checkChunk_sound 1078912 128 c1078912)) (Checked.append (checkChunk_sound 1079040 128 c1079040) (checkChunk_sound 1079168 128 c1079168))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1079296 128 c1079296) (checkChunk_sound 1079424 128 c1079424)) (Checked.append (checkChunk_sound 1079552 128 c1079552) (checkChunk_sound 1079680 128 c1079680))) (Checked.append (Checked.append (checkChunk_sound 1079808 128 c1079808) (checkChunk_sound 1079936 128 c1079936)) (Checked.append (checkChunk_sound 1080064 128 c1080064) (checkChunk_sound 1080192 128 c1080192)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1080320 128 c1080320) (checkChunk_sound 1080448 128 c1080448)) (Checked.append (checkChunk_sound 1080576 128 c1080576) (checkChunk_sound 1080704 128 c1080704))) (Checked.append (Checked.append (checkChunk_sound 1080832 128 c1080832) (checkChunk_sound 1080960 128 c1080960)) (Checked.append (checkChunk_sound 1081088 128 c1081088) (checkChunk_sound 1081216 128 c1081216)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B000
