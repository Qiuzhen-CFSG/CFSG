module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1040384, 1048576).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B022
private theorem c1040384 : checkChunk 1040384 128 = true := by decide +kernel
private theorem c1040512 : checkChunk 1040512 128 = true := by decide +kernel
private theorem c1040640 : checkChunk 1040640 128 = true := by decide +kernel
private theorem c1040768 : checkChunk 1040768 128 = true := by decide +kernel
private theorem c1040896 : checkChunk 1040896 128 = true := by decide +kernel
private theorem c1041024 : checkChunk 1041024 128 = true := by decide +kernel
private theorem c1041152 : checkChunk 1041152 128 = true := by decide +kernel
private theorem c1041280 : checkChunk 1041280 128 = true := by decide +kernel
private theorem c1041408 : checkChunk 1041408 128 = true := by decide +kernel
private theorem c1041536 : checkChunk 1041536 128 = true := by decide +kernel
private theorem c1041664 : checkChunk 1041664 128 = true := by decide +kernel
private theorem c1041792 : checkChunk 1041792 128 = true := by decide +kernel
private theorem c1041920 : checkChunk 1041920 128 = true := by decide +kernel
private theorem c1042048 : checkChunk 1042048 128 = true := by decide +kernel
private theorem c1042176 : checkChunk 1042176 128 = true := by decide +kernel
private theorem c1042304 : checkChunk 1042304 128 = true := by decide +kernel
private theorem c1042432 : checkChunk 1042432 128 = true := by decide +kernel
private theorem c1042560 : checkChunk 1042560 128 = true := by decide +kernel
private theorem c1042688 : checkChunk 1042688 128 = true := by decide +kernel
private theorem c1042816 : checkChunk 1042816 128 = true := by decide +kernel
private theorem c1042944 : checkChunk 1042944 128 = true := by decide +kernel
private theorem c1043072 : checkChunk 1043072 128 = true := by decide +kernel
private theorem c1043200 : checkChunk 1043200 128 = true := by decide +kernel
private theorem c1043328 : checkChunk 1043328 128 = true := by decide +kernel
private theorem c1043456 : checkChunk 1043456 128 = true := by decide +kernel
private theorem c1043584 : checkChunk 1043584 128 = true := by decide +kernel
private theorem c1043712 : checkChunk 1043712 128 = true := by decide +kernel
private theorem c1043840 : checkChunk 1043840 128 = true := by decide +kernel
private theorem c1043968 : checkChunk 1043968 128 = true := by decide +kernel
private theorem c1044096 : checkChunk 1044096 128 = true := by decide +kernel
private theorem c1044224 : checkChunk 1044224 128 = true := by decide +kernel
private theorem c1044352 : checkChunk 1044352 128 = true := by decide +kernel
private theorem c1044480 : checkChunk 1044480 128 = true := by decide +kernel
private theorem c1044608 : checkChunk 1044608 128 = true := by decide +kernel
private theorem c1044736 : checkChunk 1044736 128 = true := by decide +kernel
private theorem c1044864 : checkChunk 1044864 128 = true := by decide +kernel
private theorem c1044992 : checkChunk 1044992 128 = true := by decide +kernel
private theorem c1045120 : checkChunk 1045120 128 = true := by decide +kernel
private theorem c1045248 : checkChunk 1045248 128 = true := by decide +kernel
private theorem c1045376 : checkChunk 1045376 128 = true := by decide +kernel
private theorem c1045504 : checkChunk 1045504 128 = true := by decide +kernel
private theorem c1045632 : checkChunk 1045632 128 = true := by decide +kernel
private theorem c1045760 : checkChunk 1045760 128 = true := by decide +kernel
private theorem c1045888 : checkChunk 1045888 128 = true := by decide +kernel
private theorem c1046016 : checkChunk 1046016 128 = true := by decide +kernel
private theorem c1046144 : checkChunk 1046144 128 = true := by decide +kernel
private theorem c1046272 : checkChunk 1046272 128 = true := by decide +kernel
private theorem c1046400 : checkChunk 1046400 128 = true := by decide +kernel
private theorem c1046528 : checkChunk 1046528 128 = true := by decide +kernel
private theorem c1046656 : checkChunk 1046656 128 = true := by decide +kernel
private theorem c1046784 : checkChunk 1046784 128 = true := by decide +kernel
private theorem c1046912 : checkChunk 1046912 128 = true := by decide +kernel
private theorem c1047040 : checkChunk 1047040 128 = true := by decide +kernel
private theorem c1047168 : checkChunk 1047168 128 = true := by decide +kernel
private theorem c1047296 : checkChunk 1047296 128 = true := by decide +kernel
private theorem c1047424 : checkChunk 1047424 128 = true := by decide +kernel
private theorem c1047552 : checkChunk 1047552 128 = true := by decide +kernel
private theorem c1047680 : checkChunk 1047680 128 = true := by decide +kernel
private theorem c1047808 : checkChunk 1047808 128 = true := by decide +kernel
private theorem c1047936 : checkChunk 1047936 128 = true := by decide +kernel
private theorem c1048064 : checkChunk 1048064 128 = true := by decide +kernel
private theorem c1048192 : checkChunk 1048192 128 = true := by decide +kernel
private theorem c1048320 : checkChunk 1048320 128 = true := by decide +kernel
private theorem c1048448 : checkChunk 1048448 128 = true := by decide +kernel

public theorem checked : Checked 1040384 1048576 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1040384 128 c1040384) (checkChunk_sound 1040512 128 c1040512)) (Checked.append (checkChunk_sound 1040640 128 c1040640) (checkChunk_sound 1040768 128 c1040768))) (Checked.append (Checked.append (checkChunk_sound 1040896 128 c1040896) (checkChunk_sound 1041024 128 c1041024)) (Checked.append (checkChunk_sound 1041152 128 c1041152) (checkChunk_sound 1041280 128 c1041280)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1041408 128 c1041408) (checkChunk_sound 1041536 128 c1041536)) (Checked.append (checkChunk_sound 1041664 128 c1041664) (checkChunk_sound 1041792 128 c1041792))) (Checked.append (Checked.append (checkChunk_sound 1041920 128 c1041920) (checkChunk_sound 1042048 128 c1042048)) (Checked.append (checkChunk_sound 1042176 128 c1042176) (checkChunk_sound 1042304 128 c1042304))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1042432 128 c1042432) (checkChunk_sound 1042560 128 c1042560)) (Checked.append (checkChunk_sound 1042688 128 c1042688) (checkChunk_sound 1042816 128 c1042816))) (Checked.append (Checked.append (checkChunk_sound 1042944 128 c1042944) (checkChunk_sound 1043072 128 c1043072)) (Checked.append (checkChunk_sound 1043200 128 c1043200) (checkChunk_sound 1043328 128 c1043328)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1043456 128 c1043456) (checkChunk_sound 1043584 128 c1043584)) (Checked.append (checkChunk_sound 1043712 128 c1043712) (checkChunk_sound 1043840 128 c1043840))) (Checked.append (Checked.append (checkChunk_sound 1043968 128 c1043968) (checkChunk_sound 1044096 128 c1044096)) (Checked.append (checkChunk_sound 1044224 128 c1044224) (checkChunk_sound 1044352 128 c1044352)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1044480 128 c1044480) (checkChunk_sound 1044608 128 c1044608)) (Checked.append (checkChunk_sound 1044736 128 c1044736) (checkChunk_sound 1044864 128 c1044864))) (Checked.append (Checked.append (checkChunk_sound 1044992 128 c1044992) (checkChunk_sound 1045120 128 c1045120)) (Checked.append (checkChunk_sound 1045248 128 c1045248) (checkChunk_sound 1045376 128 c1045376)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1045504 128 c1045504) (checkChunk_sound 1045632 128 c1045632)) (Checked.append (checkChunk_sound 1045760 128 c1045760) (checkChunk_sound 1045888 128 c1045888))) (Checked.append (Checked.append (checkChunk_sound 1046016 128 c1046016) (checkChunk_sound 1046144 128 c1046144)) (Checked.append (checkChunk_sound 1046272 128 c1046272) (checkChunk_sound 1046400 128 c1046400))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1046528 128 c1046528) (checkChunk_sound 1046656 128 c1046656)) (Checked.append (checkChunk_sound 1046784 128 c1046784) (checkChunk_sound 1046912 128 c1046912))) (Checked.append (Checked.append (checkChunk_sound 1047040 128 c1047040) (checkChunk_sound 1047168 128 c1047168)) (Checked.append (checkChunk_sound 1047296 128 c1047296) (checkChunk_sound 1047424 128 c1047424)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1047552 128 c1047552) (checkChunk_sound 1047680 128 c1047680)) (Checked.append (checkChunk_sound 1047808 128 c1047808) (checkChunk_sound 1047936 128 c1047936))) (Checked.append (Checked.append (checkChunk_sound 1048064 128 c1048064) (checkChunk_sound 1048192 128 c1048192)) (Checked.append (checkChunk_sound 1048320 128 c1048320) (checkChunk_sound 1048448 128 c1048448)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B022
