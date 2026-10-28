module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1056768, 1064960).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B024
private theorem c1056768 : checkChunk 1056768 128 = true := by decide +kernel
private theorem c1056896 : checkChunk 1056896 128 = true := by decide +kernel
private theorem c1057024 : checkChunk 1057024 128 = true := by decide +kernel
private theorem c1057152 : checkChunk 1057152 128 = true := by decide +kernel
private theorem c1057280 : checkChunk 1057280 128 = true := by decide +kernel
private theorem c1057408 : checkChunk 1057408 128 = true := by decide +kernel
private theorem c1057536 : checkChunk 1057536 128 = true := by decide +kernel
private theorem c1057664 : checkChunk 1057664 128 = true := by decide +kernel
private theorem c1057792 : checkChunk 1057792 128 = true := by decide +kernel
private theorem c1057920 : checkChunk 1057920 128 = true := by decide +kernel
private theorem c1058048 : checkChunk 1058048 128 = true := by decide +kernel
private theorem c1058176 : checkChunk 1058176 128 = true := by decide +kernel
private theorem c1058304 : checkChunk 1058304 128 = true := by decide +kernel
private theorem c1058432 : checkChunk 1058432 128 = true := by decide +kernel
private theorem c1058560 : checkChunk 1058560 128 = true := by decide +kernel
private theorem c1058688 : checkChunk 1058688 128 = true := by decide +kernel
private theorem c1058816 : checkChunk 1058816 128 = true := by decide +kernel
private theorem c1058944 : checkChunk 1058944 128 = true := by decide +kernel
private theorem c1059072 : checkChunk 1059072 128 = true := by decide +kernel
private theorem c1059200 : checkChunk 1059200 128 = true := by decide +kernel
private theorem c1059328 : checkChunk 1059328 128 = true := by decide +kernel
private theorem c1059456 : checkChunk 1059456 128 = true := by decide +kernel
private theorem c1059584 : checkChunk 1059584 128 = true := by decide +kernel
private theorem c1059712 : checkChunk 1059712 128 = true := by decide +kernel
private theorem c1059840 : checkChunk 1059840 128 = true := by decide +kernel
private theorem c1059968 : checkChunk 1059968 128 = true := by decide +kernel
private theorem c1060096 : checkChunk 1060096 128 = true := by decide +kernel
private theorem c1060224 : checkChunk 1060224 128 = true := by decide +kernel
private theorem c1060352 : checkChunk 1060352 128 = true := by decide +kernel
private theorem c1060480 : checkChunk 1060480 128 = true := by decide +kernel
private theorem c1060608 : checkChunk 1060608 128 = true := by decide +kernel
private theorem c1060736 : checkChunk 1060736 128 = true := by decide +kernel
private theorem c1060864 : checkChunk 1060864 128 = true := by decide +kernel
private theorem c1060992 : checkChunk 1060992 128 = true := by decide +kernel
private theorem c1061120 : checkChunk 1061120 128 = true := by decide +kernel
private theorem c1061248 : checkChunk 1061248 128 = true := by decide +kernel
private theorem c1061376 : checkChunk 1061376 128 = true := by decide +kernel
private theorem c1061504 : checkChunk 1061504 128 = true := by decide +kernel
private theorem c1061632 : checkChunk 1061632 128 = true := by decide +kernel
private theorem c1061760 : checkChunk 1061760 128 = true := by decide +kernel
private theorem c1061888 : checkChunk 1061888 128 = true := by decide +kernel
private theorem c1062016 : checkChunk 1062016 128 = true := by decide +kernel
private theorem c1062144 : checkChunk 1062144 128 = true := by decide +kernel
private theorem c1062272 : checkChunk 1062272 128 = true := by decide +kernel
private theorem c1062400 : checkChunk 1062400 128 = true := by decide +kernel
private theorem c1062528 : checkChunk 1062528 128 = true := by decide +kernel
private theorem c1062656 : checkChunk 1062656 128 = true := by decide +kernel
private theorem c1062784 : checkChunk 1062784 128 = true := by decide +kernel
private theorem c1062912 : checkChunk 1062912 128 = true := by decide +kernel
private theorem c1063040 : checkChunk 1063040 128 = true := by decide +kernel
private theorem c1063168 : checkChunk 1063168 128 = true := by decide +kernel
private theorem c1063296 : checkChunk 1063296 128 = true := by decide +kernel
private theorem c1063424 : checkChunk 1063424 128 = true := by decide +kernel
private theorem c1063552 : checkChunk 1063552 128 = true := by decide +kernel
private theorem c1063680 : checkChunk 1063680 128 = true := by decide +kernel
private theorem c1063808 : checkChunk 1063808 128 = true := by decide +kernel
private theorem c1063936 : checkChunk 1063936 128 = true := by decide +kernel
private theorem c1064064 : checkChunk 1064064 128 = true := by decide +kernel
private theorem c1064192 : checkChunk 1064192 128 = true := by decide +kernel
private theorem c1064320 : checkChunk 1064320 128 = true := by decide +kernel
private theorem c1064448 : checkChunk 1064448 128 = true := by decide +kernel
private theorem c1064576 : checkChunk 1064576 128 = true := by decide +kernel
private theorem c1064704 : checkChunk 1064704 128 = true := by decide +kernel
private theorem c1064832 : checkChunk 1064832 128 = true := by decide +kernel

public theorem checked : Checked 1056768 1064960 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1056768 128 c1056768) (checkChunk_sound 1056896 128 c1056896)) (Checked.append (checkChunk_sound 1057024 128 c1057024) (checkChunk_sound 1057152 128 c1057152))) (Checked.append (Checked.append (checkChunk_sound 1057280 128 c1057280) (checkChunk_sound 1057408 128 c1057408)) (Checked.append (checkChunk_sound 1057536 128 c1057536) (checkChunk_sound 1057664 128 c1057664)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1057792 128 c1057792) (checkChunk_sound 1057920 128 c1057920)) (Checked.append (checkChunk_sound 1058048 128 c1058048) (checkChunk_sound 1058176 128 c1058176))) (Checked.append (Checked.append (checkChunk_sound 1058304 128 c1058304) (checkChunk_sound 1058432 128 c1058432)) (Checked.append (checkChunk_sound 1058560 128 c1058560) (checkChunk_sound 1058688 128 c1058688))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1058816 128 c1058816) (checkChunk_sound 1058944 128 c1058944)) (Checked.append (checkChunk_sound 1059072 128 c1059072) (checkChunk_sound 1059200 128 c1059200))) (Checked.append (Checked.append (checkChunk_sound 1059328 128 c1059328) (checkChunk_sound 1059456 128 c1059456)) (Checked.append (checkChunk_sound 1059584 128 c1059584) (checkChunk_sound 1059712 128 c1059712)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1059840 128 c1059840) (checkChunk_sound 1059968 128 c1059968)) (Checked.append (checkChunk_sound 1060096 128 c1060096) (checkChunk_sound 1060224 128 c1060224))) (Checked.append (Checked.append (checkChunk_sound 1060352 128 c1060352) (checkChunk_sound 1060480 128 c1060480)) (Checked.append (checkChunk_sound 1060608 128 c1060608) (checkChunk_sound 1060736 128 c1060736)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1060864 128 c1060864) (checkChunk_sound 1060992 128 c1060992)) (Checked.append (checkChunk_sound 1061120 128 c1061120) (checkChunk_sound 1061248 128 c1061248))) (Checked.append (Checked.append (checkChunk_sound 1061376 128 c1061376) (checkChunk_sound 1061504 128 c1061504)) (Checked.append (checkChunk_sound 1061632 128 c1061632) (checkChunk_sound 1061760 128 c1061760)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1061888 128 c1061888) (checkChunk_sound 1062016 128 c1062016)) (Checked.append (checkChunk_sound 1062144 128 c1062144) (checkChunk_sound 1062272 128 c1062272))) (Checked.append (Checked.append (checkChunk_sound 1062400 128 c1062400) (checkChunk_sound 1062528 128 c1062528)) (Checked.append (checkChunk_sound 1062656 128 c1062656) (checkChunk_sound 1062784 128 c1062784))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1062912 128 c1062912) (checkChunk_sound 1063040 128 c1063040)) (Checked.append (checkChunk_sound 1063168 128 c1063168) (checkChunk_sound 1063296 128 c1063296))) (Checked.append (Checked.append (checkChunk_sound 1063424 128 c1063424) (checkChunk_sound 1063552 128 c1063552)) (Checked.append (checkChunk_sound 1063680 128 c1063680) (checkChunk_sound 1063808 128 c1063808)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1063936 128 c1063936) (checkChunk_sound 1064064 128 c1064064)) (Checked.append (checkChunk_sound 1064192 128 c1064192) (checkChunk_sound 1064320 128 c1064320))) (Checked.append (Checked.append (checkChunk_sound 1064448 128 c1064448) (checkChunk_sound 1064576 128 c1064576)) (Checked.append (checkChunk_sound 1064704 128 c1064704) (checkChunk_sound 1064832 128 c1064832)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B024
