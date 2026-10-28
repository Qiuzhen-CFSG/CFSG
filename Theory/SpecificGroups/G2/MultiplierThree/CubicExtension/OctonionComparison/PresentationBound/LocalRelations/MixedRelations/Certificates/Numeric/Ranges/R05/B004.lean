module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1105920, 1114112).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B004
private theorem c1105920 : checkChunk 1105920 128 = true := by decide +kernel
private theorem c1106048 : checkChunk 1106048 128 = true := by decide +kernel
private theorem c1106176 : checkChunk 1106176 128 = true := by decide +kernel
private theorem c1106304 : checkChunk 1106304 128 = true := by decide +kernel
private theorem c1106432 : checkChunk 1106432 128 = true := by decide +kernel
private theorem c1106560 : checkChunk 1106560 128 = true := by decide +kernel
private theorem c1106688 : checkChunk 1106688 128 = true := by decide +kernel
private theorem c1106816 : checkChunk 1106816 128 = true := by decide +kernel
private theorem c1106944 : checkChunk 1106944 128 = true := by decide +kernel
private theorem c1107072 : checkChunk 1107072 128 = true := by decide +kernel
private theorem c1107200 : checkChunk 1107200 128 = true := by decide +kernel
private theorem c1107328 : checkChunk 1107328 128 = true := by decide +kernel
private theorem c1107456 : checkChunk 1107456 128 = true := by decide +kernel
private theorem c1107584 : checkChunk 1107584 128 = true := by decide +kernel
private theorem c1107712 : checkChunk 1107712 128 = true := by decide +kernel
private theorem c1107840 : checkChunk 1107840 128 = true := by decide +kernel
private theorem c1107968 : checkChunk 1107968 128 = true := by decide +kernel
private theorem c1108096 : checkChunk 1108096 128 = true := by decide +kernel
private theorem c1108224 : checkChunk 1108224 128 = true := by decide +kernel
private theorem c1108352 : checkChunk 1108352 128 = true := by decide +kernel
private theorem c1108480 : checkChunk 1108480 128 = true := by decide +kernel
private theorem c1108608 : checkChunk 1108608 128 = true := by decide +kernel
private theorem c1108736 : checkChunk 1108736 128 = true := by decide +kernel
private theorem c1108864 : checkChunk 1108864 128 = true := by decide +kernel
private theorem c1108992 : checkChunk 1108992 128 = true := by decide +kernel
private theorem c1109120 : checkChunk 1109120 128 = true := by decide +kernel
private theorem c1109248 : checkChunk 1109248 128 = true := by decide +kernel
private theorem c1109376 : checkChunk 1109376 128 = true := by decide +kernel
private theorem c1109504 : checkChunk 1109504 128 = true := by decide +kernel
private theorem c1109632 : checkChunk 1109632 128 = true := by decide +kernel
private theorem c1109760 : checkChunk 1109760 128 = true := by decide +kernel
private theorem c1109888 : checkChunk 1109888 128 = true := by decide +kernel
private theorem c1110016 : checkChunk 1110016 128 = true := by decide +kernel
private theorem c1110144 : checkChunk 1110144 128 = true := by decide +kernel
private theorem c1110272 : checkChunk 1110272 128 = true := by decide +kernel
private theorem c1110400 : checkChunk 1110400 128 = true := by decide +kernel
private theorem c1110528 : checkChunk 1110528 128 = true := by decide +kernel
private theorem c1110656 : checkChunk 1110656 128 = true := by decide +kernel
private theorem c1110784 : checkChunk 1110784 128 = true := by decide +kernel
private theorem c1110912 : checkChunk 1110912 128 = true := by decide +kernel
private theorem c1111040 : checkChunk 1111040 128 = true := by decide +kernel
private theorem c1111168 : checkChunk 1111168 128 = true := by decide +kernel
private theorem c1111296 : checkChunk 1111296 128 = true := by decide +kernel
private theorem c1111424 : checkChunk 1111424 128 = true := by decide +kernel
private theorem c1111552 : checkChunk 1111552 128 = true := by decide +kernel
private theorem c1111680 : checkChunk 1111680 128 = true := by decide +kernel
private theorem c1111808 : checkChunk 1111808 128 = true := by decide +kernel
private theorem c1111936 : checkChunk 1111936 128 = true := by decide +kernel
private theorem c1112064 : checkChunk 1112064 128 = true := by decide +kernel
private theorem c1112192 : checkChunk 1112192 128 = true := by decide +kernel
private theorem c1112320 : checkChunk 1112320 128 = true := by decide +kernel
private theorem c1112448 : checkChunk 1112448 128 = true := by decide +kernel
private theorem c1112576 : checkChunk 1112576 128 = true := by decide +kernel
private theorem c1112704 : checkChunk 1112704 128 = true := by decide +kernel
private theorem c1112832 : checkChunk 1112832 128 = true := by decide +kernel
private theorem c1112960 : checkChunk 1112960 128 = true := by decide +kernel
private theorem c1113088 : checkChunk 1113088 128 = true := by decide +kernel
private theorem c1113216 : checkChunk 1113216 128 = true := by decide +kernel
private theorem c1113344 : checkChunk 1113344 128 = true := by decide +kernel
private theorem c1113472 : checkChunk 1113472 128 = true := by decide +kernel
private theorem c1113600 : checkChunk 1113600 128 = true := by decide +kernel
private theorem c1113728 : checkChunk 1113728 128 = true := by decide +kernel
private theorem c1113856 : checkChunk 1113856 128 = true := by decide +kernel
private theorem c1113984 : checkChunk 1113984 128 = true := by decide +kernel

public theorem checked : Checked 1105920 1114112 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1105920 128 c1105920) (checkChunk_sound 1106048 128 c1106048)) (Checked.append (checkChunk_sound 1106176 128 c1106176) (checkChunk_sound 1106304 128 c1106304))) (Checked.append (Checked.append (checkChunk_sound 1106432 128 c1106432) (checkChunk_sound 1106560 128 c1106560)) (Checked.append (checkChunk_sound 1106688 128 c1106688) (checkChunk_sound 1106816 128 c1106816)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1106944 128 c1106944) (checkChunk_sound 1107072 128 c1107072)) (Checked.append (checkChunk_sound 1107200 128 c1107200) (checkChunk_sound 1107328 128 c1107328))) (Checked.append (Checked.append (checkChunk_sound 1107456 128 c1107456) (checkChunk_sound 1107584 128 c1107584)) (Checked.append (checkChunk_sound 1107712 128 c1107712) (checkChunk_sound 1107840 128 c1107840))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1107968 128 c1107968) (checkChunk_sound 1108096 128 c1108096)) (Checked.append (checkChunk_sound 1108224 128 c1108224) (checkChunk_sound 1108352 128 c1108352))) (Checked.append (Checked.append (checkChunk_sound 1108480 128 c1108480) (checkChunk_sound 1108608 128 c1108608)) (Checked.append (checkChunk_sound 1108736 128 c1108736) (checkChunk_sound 1108864 128 c1108864)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1108992 128 c1108992) (checkChunk_sound 1109120 128 c1109120)) (Checked.append (checkChunk_sound 1109248 128 c1109248) (checkChunk_sound 1109376 128 c1109376))) (Checked.append (Checked.append (checkChunk_sound 1109504 128 c1109504) (checkChunk_sound 1109632 128 c1109632)) (Checked.append (checkChunk_sound 1109760 128 c1109760) (checkChunk_sound 1109888 128 c1109888)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1110016 128 c1110016) (checkChunk_sound 1110144 128 c1110144)) (Checked.append (checkChunk_sound 1110272 128 c1110272) (checkChunk_sound 1110400 128 c1110400))) (Checked.append (Checked.append (checkChunk_sound 1110528 128 c1110528) (checkChunk_sound 1110656 128 c1110656)) (Checked.append (checkChunk_sound 1110784 128 c1110784) (checkChunk_sound 1110912 128 c1110912)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1111040 128 c1111040) (checkChunk_sound 1111168 128 c1111168)) (Checked.append (checkChunk_sound 1111296 128 c1111296) (checkChunk_sound 1111424 128 c1111424))) (Checked.append (Checked.append (checkChunk_sound 1111552 128 c1111552) (checkChunk_sound 1111680 128 c1111680)) (Checked.append (checkChunk_sound 1111808 128 c1111808) (checkChunk_sound 1111936 128 c1111936))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1112064 128 c1112064) (checkChunk_sound 1112192 128 c1112192)) (Checked.append (checkChunk_sound 1112320 128 c1112320) (checkChunk_sound 1112448 128 c1112448))) (Checked.append (Checked.append (checkChunk_sound 1112576 128 c1112576) (checkChunk_sound 1112704 128 c1112704)) (Checked.append (checkChunk_sound 1112832 128 c1112832) (checkChunk_sound 1112960 128 c1112960)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1113088 128 c1113088) (checkChunk_sound 1113216 128 c1113216)) (Checked.append (checkChunk_sound 1113344 128 c1113344) (checkChunk_sound 1113472 128 c1113472))) (Checked.append (Checked.append (checkChunk_sound 1113600 128 c1113600) (checkChunk_sound 1113728 128 c1113728)) (Checked.append (checkChunk_sound 1113856 128 c1113856) (checkChunk_sound 1113984 128 c1113984)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B004
