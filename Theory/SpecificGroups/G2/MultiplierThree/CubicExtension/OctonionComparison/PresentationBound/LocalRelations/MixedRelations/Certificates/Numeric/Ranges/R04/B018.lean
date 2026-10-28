module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1007616, 1015808).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B018
private theorem c1007616 : checkChunk 1007616 128 = true := by decide +kernel
private theorem c1007744 : checkChunk 1007744 128 = true := by decide +kernel
private theorem c1007872 : checkChunk 1007872 128 = true := by decide +kernel
private theorem c1008000 : checkChunk 1008000 128 = true := by decide +kernel
private theorem c1008128 : checkChunk 1008128 128 = true := by decide +kernel
private theorem c1008256 : checkChunk 1008256 128 = true := by decide +kernel
private theorem c1008384 : checkChunk 1008384 128 = true := by decide +kernel
private theorem c1008512 : checkChunk 1008512 128 = true := by decide +kernel
private theorem c1008640 : checkChunk 1008640 128 = true := by decide +kernel
private theorem c1008768 : checkChunk 1008768 128 = true := by decide +kernel
private theorem c1008896 : checkChunk 1008896 128 = true := by decide +kernel
private theorem c1009024 : checkChunk 1009024 128 = true := by decide +kernel
private theorem c1009152 : checkChunk 1009152 128 = true := by decide +kernel
private theorem c1009280 : checkChunk 1009280 128 = true := by decide +kernel
private theorem c1009408 : checkChunk 1009408 128 = true := by decide +kernel
private theorem c1009536 : checkChunk 1009536 128 = true := by decide +kernel
private theorem c1009664 : checkChunk 1009664 128 = true := by decide +kernel
private theorem c1009792 : checkChunk 1009792 128 = true := by decide +kernel
private theorem c1009920 : checkChunk 1009920 128 = true := by decide +kernel
private theorem c1010048 : checkChunk 1010048 128 = true := by decide +kernel
private theorem c1010176 : checkChunk 1010176 128 = true := by decide +kernel
private theorem c1010304 : checkChunk 1010304 128 = true := by decide +kernel
private theorem c1010432 : checkChunk 1010432 128 = true := by decide +kernel
private theorem c1010560 : checkChunk 1010560 128 = true := by decide +kernel
private theorem c1010688 : checkChunk 1010688 128 = true := by decide +kernel
private theorem c1010816 : checkChunk 1010816 128 = true := by decide +kernel
private theorem c1010944 : checkChunk 1010944 128 = true := by decide +kernel
private theorem c1011072 : checkChunk 1011072 128 = true := by decide +kernel
private theorem c1011200 : checkChunk 1011200 128 = true := by decide +kernel
private theorem c1011328 : checkChunk 1011328 128 = true := by decide +kernel
private theorem c1011456 : checkChunk 1011456 128 = true := by decide +kernel
private theorem c1011584 : checkChunk 1011584 128 = true := by decide +kernel
private theorem c1011712 : checkChunk 1011712 128 = true := by decide +kernel
private theorem c1011840 : checkChunk 1011840 128 = true := by decide +kernel
private theorem c1011968 : checkChunk 1011968 128 = true := by decide +kernel
private theorem c1012096 : checkChunk 1012096 128 = true := by decide +kernel
private theorem c1012224 : checkChunk 1012224 128 = true := by decide +kernel
private theorem c1012352 : checkChunk 1012352 128 = true := by decide +kernel
private theorem c1012480 : checkChunk 1012480 128 = true := by decide +kernel
private theorem c1012608 : checkChunk 1012608 128 = true := by decide +kernel
private theorem c1012736 : checkChunk 1012736 128 = true := by decide +kernel
private theorem c1012864 : checkChunk 1012864 128 = true := by decide +kernel
private theorem c1012992 : checkChunk 1012992 128 = true := by decide +kernel
private theorem c1013120 : checkChunk 1013120 128 = true := by decide +kernel
private theorem c1013248 : checkChunk 1013248 128 = true := by decide +kernel
private theorem c1013376 : checkChunk 1013376 128 = true := by decide +kernel
private theorem c1013504 : checkChunk 1013504 128 = true := by decide +kernel
private theorem c1013632 : checkChunk 1013632 128 = true := by decide +kernel
private theorem c1013760 : checkChunk 1013760 128 = true := by decide +kernel
private theorem c1013888 : checkChunk 1013888 128 = true := by decide +kernel
private theorem c1014016 : checkChunk 1014016 128 = true := by decide +kernel
private theorem c1014144 : checkChunk 1014144 128 = true := by decide +kernel
private theorem c1014272 : checkChunk 1014272 128 = true := by decide +kernel
private theorem c1014400 : checkChunk 1014400 128 = true := by decide +kernel
private theorem c1014528 : checkChunk 1014528 128 = true := by decide +kernel
private theorem c1014656 : checkChunk 1014656 128 = true := by decide +kernel
private theorem c1014784 : checkChunk 1014784 128 = true := by decide +kernel
private theorem c1014912 : checkChunk 1014912 128 = true := by decide +kernel
private theorem c1015040 : checkChunk 1015040 128 = true := by decide +kernel
private theorem c1015168 : checkChunk 1015168 128 = true := by decide +kernel
private theorem c1015296 : checkChunk 1015296 128 = true := by decide +kernel
private theorem c1015424 : checkChunk 1015424 128 = true := by decide +kernel
private theorem c1015552 : checkChunk 1015552 128 = true := by decide +kernel
private theorem c1015680 : checkChunk 1015680 128 = true := by decide +kernel

public theorem checked : Checked 1007616 1015808 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1007616 128 c1007616) (checkChunk_sound 1007744 128 c1007744)) (Checked.append (checkChunk_sound 1007872 128 c1007872) (checkChunk_sound 1008000 128 c1008000))) (Checked.append (Checked.append (checkChunk_sound 1008128 128 c1008128) (checkChunk_sound 1008256 128 c1008256)) (Checked.append (checkChunk_sound 1008384 128 c1008384) (checkChunk_sound 1008512 128 c1008512)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1008640 128 c1008640) (checkChunk_sound 1008768 128 c1008768)) (Checked.append (checkChunk_sound 1008896 128 c1008896) (checkChunk_sound 1009024 128 c1009024))) (Checked.append (Checked.append (checkChunk_sound 1009152 128 c1009152) (checkChunk_sound 1009280 128 c1009280)) (Checked.append (checkChunk_sound 1009408 128 c1009408) (checkChunk_sound 1009536 128 c1009536))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1009664 128 c1009664) (checkChunk_sound 1009792 128 c1009792)) (Checked.append (checkChunk_sound 1009920 128 c1009920) (checkChunk_sound 1010048 128 c1010048))) (Checked.append (Checked.append (checkChunk_sound 1010176 128 c1010176) (checkChunk_sound 1010304 128 c1010304)) (Checked.append (checkChunk_sound 1010432 128 c1010432) (checkChunk_sound 1010560 128 c1010560)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1010688 128 c1010688) (checkChunk_sound 1010816 128 c1010816)) (Checked.append (checkChunk_sound 1010944 128 c1010944) (checkChunk_sound 1011072 128 c1011072))) (Checked.append (Checked.append (checkChunk_sound 1011200 128 c1011200) (checkChunk_sound 1011328 128 c1011328)) (Checked.append (checkChunk_sound 1011456 128 c1011456) (checkChunk_sound 1011584 128 c1011584)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1011712 128 c1011712) (checkChunk_sound 1011840 128 c1011840)) (Checked.append (checkChunk_sound 1011968 128 c1011968) (checkChunk_sound 1012096 128 c1012096))) (Checked.append (Checked.append (checkChunk_sound 1012224 128 c1012224) (checkChunk_sound 1012352 128 c1012352)) (Checked.append (checkChunk_sound 1012480 128 c1012480) (checkChunk_sound 1012608 128 c1012608)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1012736 128 c1012736) (checkChunk_sound 1012864 128 c1012864)) (Checked.append (checkChunk_sound 1012992 128 c1012992) (checkChunk_sound 1013120 128 c1013120))) (Checked.append (Checked.append (checkChunk_sound 1013248 128 c1013248) (checkChunk_sound 1013376 128 c1013376)) (Checked.append (checkChunk_sound 1013504 128 c1013504) (checkChunk_sound 1013632 128 c1013632))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1013760 128 c1013760) (checkChunk_sound 1013888 128 c1013888)) (Checked.append (checkChunk_sound 1014016 128 c1014016) (checkChunk_sound 1014144 128 c1014144))) (Checked.append (Checked.append (checkChunk_sound 1014272 128 c1014272) (checkChunk_sound 1014400 128 c1014400)) (Checked.append (checkChunk_sound 1014528 128 c1014528) (checkChunk_sound 1014656 128 c1014656)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1014784 128 c1014784) (checkChunk_sound 1014912 128 c1014912)) (Checked.append (checkChunk_sound 1015040 128 c1015040) (checkChunk_sound 1015168 128 c1015168))) (Checked.append (Checked.append (checkChunk_sound 1015296 128 c1015296) (checkChunk_sound 1015424 128 c1015424)) (Checked.append (checkChunk_sound 1015552 128 c1015552) (checkChunk_sound 1015680 128 c1015680)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B018
