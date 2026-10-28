module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [655360, 663552).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B001
private theorem c655360 : checkChunk 655360 128 = true := by decide +kernel
private theorem c655488 : checkChunk 655488 128 = true := by decide +kernel
private theorem c655616 : checkChunk 655616 128 = true := by decide +kernel
private theorem c655744 : checkChunk 655744 128 = true := by decide +kernel
private theorem c655872 : checkChunk 655872 128 = true := by decide +kernel
private theorem c656000 : checkChunk 656000 128 = true := by decide +kernel
private theorem c656128 : checkChunk 656128 128 = true := by decide +kernel
private theorem c656256 : checkChunk 656256 128 = true := by decide +kernel
private theorem c656384 : checkChunk 656384 128 = true := by decide +kernel
private theorem c656512 : checkChunk 656512 128 = true := by decide +kernel
private theorem c656640 : checkChunk 656640 128 = true := by decide +kernel
private theorem c656768 : checkChunk 656768 128 = true := by decide +kernel
private theorem c656896 : checkChunk 656896 128 = true := by decide +kernel
private theorem c657024 : checkChunk 657024 128 = true := by decide +kernel
private theorem c657152 : checkChunk 657152 128 = true := by decide +kernel
private theorem c657280 : checkChunk 657280 128 = true := by decide +kernel
private theorem c657408 : checkChunk 657408 128 = true := by decide +kernel
private theorem c657536 : checkChunk 657536 128 = true := by decide +kernel
private theorem c657664 : checkChunk 657664 128 = true := by decide +kernel
private theorem c657792 : checkChunk 657792 128 = true := by decide +kernel
private theorem c657920 : checkChunk 657920 128 = true := by decide +kernel
private theorem c658048 : checkChunk 658048 128 = true := by decide +kernel
private theorem c658176 : checkChunk 658176 128 = true := by decide +kernel
private theorem c658304 : checkChunk 658304 128 = true := by decide +kernel
private theorem c658432 : checkChunk 658432 128 = true := by decide +kernel
private theorem c658560 : checkChunk 658560 128 = true := by decide +kernel
private theorem c658688 : checkChunk 658688 128 = true := by decide +kernel
private theorem c658816 : checkChunk 658816 128 = true := by decide +kernel
private theorem c658944 : checkChunk 658944 128 = true := by decide +kernel
private theorem c659072 : checkChunk 659072 128 = true := by decide +kernel
private theorem c659200 : checkChunk 659200 128 = true := by decide +kernel
private theorem c659328 : checkChunk 659328 128 = true := by decide +kernel
private theorem c659456 : checkChunk 659456 128 = true := by decide +kernel
private theorem c659584 : checkChunk 659584 128 = true := by decide +kernel
private theorem c659712 : checkChunk 659712 128 = true := by decide +kernel
private theorem c659840 : checkChunk 659840 128 = true := by decide +kernel
private theorem c659968 : checkChunk 659968 128 = true := by decide +kernel
private theorem c660096 : checkChunk 660096 128 = true := by decide +kernel
private theorem c660224 : checkChunk 660224 128 = true := by decide +kernel
private theorem c660352 : checkChunk 660352 128 = true := by decide +kernel
private theorem c660480 : checkChunk 660480 128 = true := by decide +kernel
private theorem c660608 : checkChunk 660608 128 = true := by decide +kernel
private theorem c660736 : checkChunk 660736 128 = true := by decide +kernel
private theorem c660864 : checkChunk 660864 128 = true := by decide +kernel
private theorem c660992 : checkChunk 660992 128 = true := by decide +kernel
private theorem c661120 : checkChunk 661120 128 = true := by decide +kernel
private theorem c661248 : checkChunk 661248 128 = true := by decide +kernel
private theorem c661376 : checkChunk 661376 128 = true := by decide +kernel
private theorem c661504 : checkChunk 661504 128 = true := by decide +kernel
private theorem c661632 : checkChunk 661632 128 = true := by decide +kernel
private theorem c661760 : checkChunk 661760 128 = true := by decide +kernel
private theorem c661888 : checkChunk 661888 128 = true := by decide +kernel
private theorem c662016 : checkChunk 662016 128 = true := by decide +kernel
private theorem c662144 : checkChunk 662144 128 = true := by decide +kernel
private theorem c662272 : checkChunk 662272 128 = true := by decide +kernel
private theorem c662400 : checkChunk 662400 128 = true := by decide +kernel
private theorem c662528 : checkChunk 662528 128 = true := by decide +kernel
private theorem c662656 : checkChunk 662656 128 = true := by decide +kernel
private theorem c662784 : checkChunk 662784 128 = true := by decide +kernel
private theorem c662912 : checkChunk 662912 128 = true := by decide +kernel
private theorem c663040 : checkChunk 663040 128 = true := by decide +kernel
private theorem c663168 : checkChunk 663168 128 = true := by decide +kernel
private theorem c663296 : checkChunk 663296 128 = true := by decide +kernel
private theorem c663424 : checkChunk 663424 128 = true := by decide +kernel

public theorem checked : Checked 655360 663552 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 655360 128 c655360) (checkChunk_sound 655488 128 c655488)) (Checked.append (checkChunk_sound 655616 128 c655616) (checkChunk_sound 655744 128 c655744))) (Checked.append (Checked.append (checkChunk_sound 655872 128 c655872) (checkChunk_sound 656000 128 c656000)) (Checked.append (checkChunk_sound 656128 128 c656128) (checkChunk_sound 656256 128 c656256)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 656384 128 c656384) (checkChunk_sound 656512 128 c656512)) (Checked.append (checkChunk_sound 656640 128 c656640) (checkChunk_sound 656768 128 c656768))) (Checked.append (Checked.append (checkChunk_sound 656896 128 c656896) (checkChunk_sound 657024 128 c657024)) (Checked.append (checkChunk_sound 657152 128 c657152) (checkChunk_sound 657280 128 c657280))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 657408 128 c657408) (checkChunk_sound 657536 128 c657536)) (Checked.append (checkChunk_sound 657664 128 c657664) (checkChunk_sound 657792 128 c657792))) (Checked.append (Checked.append (checkChunk_sound 657920 128 c657920) (checkChunk_sound 658048 128 c658048)) (Checked.append (checkChunk_sound 658176 128 c658176) (checkChunk_sound 658304 128 c658304)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 658432 128 c658432) (checkChunk_sound 658560 128 c658560)) (Checked.append (checkChunk_sound 658688 128 c658688) (checkChunk_sound 658816 128 c658816))) (Checked.append (Checked.append (checkChunk_sound 658944 128 c658944) (checkChunk_sound 659072 128 c659072)) (Checked.append (checkChunk_sound 659200 128 c659200) (checkChunk_sound 659328 128 c659328)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 659456 128 c659456) (checkChunk_sound 659584 128 c659584)) (Checked.append (checkChunk_sound 659712 128 c659712) (checkChunk_sound 659840 128 c659840))) (Checked.append (Checked.append (checkChunk_sound 659968 128 c659968) (checkChunk_sound 660096 128 c660096)) (Checked.append (checkChunk_sound 660224 128 c660224) (checkChunk_sound 660352 128 c660352)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 660480 128 c660480) (checkChunk_sound 660608 128 c660608)) (Checked.append (checkChunk_sound 660736 128 c660736) (checkChunk_sound 660864 128 c660864))) (Checked.append (Checked.append (checkChunk_sound 660992 128 c660992) (checkChunk_sound 661120 128 c661120)) (Checked.append (checkChunk_sound 661248 128 c661248) (checkChunk_sound 661376 128 c661376))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 661504 128 c661504) (checkChunk_sound 661632 128 c661632)) (Checked.append (checkChunk_sound 661760 128 c661760) (checkChunk_sound 661888 128 c661888))) (Checked.append (Checked.append (checkChunk_sound 662016 128 c662016) (checkChunk_sound 662144 128 c662144)) (Checked.append (checkChunk_sound 662272 128 c662272) (checkChunk_sound 662400 128 c662400)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 662528 128 c662528) (checkChunk_sound 662656 128 c662656)) (Checked.append (checkChunk_sound 662784 128 c662784) (checkChunk_sound 662912 128 c662912))) (Checked.append (Checked.append (checkChunk_sound 663040 128 c663040) (checkChunk_sound 663168 128 c663168)) (Checked.append (checkChunk_sound 663296 128 c663296) (checkChunk_sound 663424 128 c663424)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B001
