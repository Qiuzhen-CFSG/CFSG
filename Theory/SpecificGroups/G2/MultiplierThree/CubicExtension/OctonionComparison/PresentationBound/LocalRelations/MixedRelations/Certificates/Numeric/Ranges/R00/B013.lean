module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [114688, 122880).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B013
private theorem c114688 : checkChunk 114688 128 = true := by decide +kernel
private theorem c114816 : checkChunk 114816 128 = true := by decide +kernel
private theorem c114944 : checkChunk 114944 128 = true := by decide +kernel
private theorem c115072 : checkChunk 115072 128 = true := by decide +kernel
private theorem c115200 : checkChunk 115200 128 = true := by decide +kernel
private theorem c115328 : checkChunk 115328 128 = true := by decide +kernel
private theorem c115456 : checkChunk 115456 128 = true := by decide +kernel
private theorem c115584 : checkChunk 115584 128 = true := by decide +kernel
private theorem c115712 : checkChunk 115712 128 = true := by decide +kernel
private theorem c115840 : checkChunk 115840 128 = true := by decide +kernel
private theorem c115968 : checkChunk 115968 128 = true := by decide +kernel
private theorem c116096 : checkChunk 116096 128 = true := by decide +kernel
private theorem c116224 : checkChunk 116224 128 = true := by decide +kernel
private theorem c116352 : checkChunk 116352 128 = true := by decide +kernel
private theorem c116480 : checkChunk 116480 128 = true := by decide +kernel
private theorem c116608 : checkChunk 116608 128 = true := by decide +kernel
private theorem c116736 : checkChunk 116736 128 = true := by decide +kernel
private theorem c116864 : checkChunk 116864 128 = true := by decide +kernel
private theorem c116992 : checkChunk 116992 128 = true := by decide +kernel
private theorem c117120 : checkChunk 117120 128 = true := by decide +kernel
private theorem c117248 : checkChunk 117248 128 = true := by decide +kernel
private theorem c117376 : checkChunk 117376 128 = true := by decide +kernel
private theorem c117504 : checkChunk 117504 128 = true := by decide +kernel
private theorem c117632 : checkChunk 117632 128 = true := by decide +kernel
private theorem c117760 : checkChunk 117760 128 = true := by decide +kernel
private theorem c117888 : checkChunk 117888 128 = true := by decide +kernel
private theorem c118016 : checkChunk 118016 128 = true := by decide +kernel
private theorem c118144 : checkChunk 118144 128 = true := by decide +kernel
private theorem c118272 : checkChunk 118272 128 = true := by decide +kernel
private theorem c118400 : checkChunk 118400 128 = true := by decide +kernel
private theorem c118528 : checkChunk 118528 128 = true := by decide +kernel
private theorem c118656 : checkChunk 118656 128 = true := by decide +kernel
private theorem c118784 : checkChunk 118784 128 = true := by decide +kernel
private theorem c118912 : checkChunk 118912 128 = true := by decide +kernel
private theorem c119040 : checkChunk 119040 128 = true := by decide +kernel
private theorem c119168 : checkChunk 119168 128 = true := by decide +kernel
private theorem c119296 : checkChunk 119296 128 = true := by decide +kernel
private theorem c119424 : checkChunk 119424 128 = true := by decide +kernel
private theorem c119552 : checkChunk 119552 128 = true := by decide +kernel
private theorem c119680 : checkChunk 119680 128 = true := by decide +kernel
private theorem c119808 : checkChunk 119808 128 = true := by decide +kernel
private theorem c119936 : checkChunk 119936 128 = true := by decide +kernel
private theorem c120064 : checkChunk 120064 128 = true := by decide +kernel
private theorem c120192 : checkChunk 120192 128 = true := by decide +kernel
private theorem c120320 : checkChunk 120320 128 = true := by decide +kernel
private theorem c120448 : checkChunk 120448 128 = true := by decide +kernel
private theorem c120576 : checkChunk 120576 128 = true := by decide +kernel
private theorem c120704 : checkChunk 120704 128 = true := by decide +kernel
private theorem c120832 : checkChunk 120832 128 = true := by decide +kernel
private theorem c120960 : checkChunk 120960 128 = true := by decide +kernel
private theorem c121088 : checkChunk 121088 128 = true := by decide +kernel
private theorem c121216 : checkChunk 121216 128 = true := by decide +kernel
private theorem c121344 : checkChunk 121344 128 = true := by decide +kernel
private theorem c121472 : checkChunk 121472 128 = true := by decide +kernel
private theorem c121600 : checkChunk 121600 128 = true := by decide +kernel
private theorem c121728 : checkChunk 121728 128 = true := by decide +kernel
private theorem c121856 : checkChunk 121856 128 = true := by decide +kernel
private theorem c121984 : checkChunk 121984 128 = true := by decide +kernel
private theorem c122112 : checkChunk 122112 128 = true := by decide +kernel
private theorem c122240 : checkChunk 122240 128 = true := by decide +kernel
private theorem c122368 : checkChunk 122368 128 = true := by decide +kernel
private theorem c122496 : checkChunk 122496 128 = true := by decide +kernel
private theorem c122624 : checkChunk 122624 128 = true := by decide +kernel
private theorem c122752 : checkChunk 122752 128 = true := by decide +kernel

public theorem checked : Checked 114688 122880 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 114688 128 c114688) (checkChunk_sound 114816 128 c114816)) (Checked.append (checkChunk_sound 114944 128 c114944) (checkChunk_sound 115072 128 c115072))) (Checked.append (Checked.append (checkChunk_sound 115200 128 c115200) (checkChunk_sound 115328 128 c115328)) (Checked.append (checkChunk_sound 115456 128 c115456) (checkChunk_sound 115584 128 c115584)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 115712 128 c115712) (checkChunk_sound 115840 128 c115840)) (Checked.append (checkChunk_sound 115968 128 c115968) (checkChunk_sound 116096 128 c116096))) (Checked.append (Checked.append (checkChunk_sound 116224 128 c116224) (checkChunk_sound 116352 128 c116352)) (Checked.append (checkChunk_sound 116480 128 c116480) (checkChunk_sound 116608 128 c116608))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 116736 128 c116736) (checkChunk_sound 116864 128 c116864)) (Checked.append (checkChunk_sound 116992 128 c116992) (checkChunk_sound 117120 128 c117120))) (Checked.append (Checked.append (checkChunk_sound 117248 128 c117248) (checkChunk_sound 117376 128 c117376)) (Checked.append (checkChunk_sound 117504 128 c117504) (checkChunk_sound 117632 128 c117632)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 117760 128 c117760) (checkChunk_sound 117888 128 c117888)) (Checked.append (checkChunk_sound 118016 128 c118016) (checkChunk_sound 118144 128 c118144))) (Checked.append (Checked.append (checkChunk_sound 118272 128 c118272) (checkChunk_sound 118400 128 c118400)) (Checked.append (checkChunk_sound 118528 128 c118528) (checkChunk_sound 118656 128 c118656)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 118784 128 c118784) (checkChunk_sound 118912 128 c118912)) (Checked.append (checkChunk_sound 119040 128 c119040) (checkChunk_sound 119168 128 c119168))) (Checked.append (Checked.append (checkChunk_sound 119296 128 c119296) (checkChunk_sound 119424 128 c119424)) (Checked.append (checkChunk_sound 119552 128 c119552) (checkChunk_sound 119680 128 c119680)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 119808 128 c119808) (checkChunk_sound 119936 128 c119936)) (Checked.append (checkChunk_sound 120064 128 c120064) (checkChunk_sound 120192 128 c120192))) (Checked.append (Checked.append (checkChunk_sound 120320 128 c120320) (checkChunk_sound 120448 128 c120448)) (Checked.append (checkChunk_sound 120576 128 c120576) (checkChunk_sound 120704 128 c120704))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 120832 128 c120832) (checkChunk_sound 120960 128 c120960)) (Checked.append (checkChunk_sound 121088 128 c121088) (checkChunk_sound 121216 128 c121216))) (Checked.append (Checked.append (checkChunk_sound 121344 128 c121344) (checkChunk_sound 121472 128 c121472)) (Checked.append (checkChunk_sound 121600 128 c121600) (checkChunk_sound 121728 128 c121728)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 121856 128 c121856) (checkChunk_sound 121984 128 c121984)) (Checked.append (checkChunk_sound 122112 128 c122112) (checkChunk_sound 122240 128 c122240))) (Checked.append (Checked.append (checkChunk_sound 122368 128 c122368) (checkChunk_sound 122496 128 c122496)) (Checked.append (checkChunk_sound 122624 128 c122624) (checkChunk_sound 122752 128 c122752)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B013
