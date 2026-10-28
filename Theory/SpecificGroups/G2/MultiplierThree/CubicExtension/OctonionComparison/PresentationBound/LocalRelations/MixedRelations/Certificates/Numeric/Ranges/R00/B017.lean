module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [147456, 155648).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B017
private theorem c147456 : checkChunk 147456 128 = true := by decide +kernel
private theorem c147584 : checkChunk 147584 128 = true := by decide +kernel
private theorem c147712 : checkChunk 147712 128 = true := by decide +kernel
private theorem c147840 : checkChunk 147840 128 = true := by decide +kernel
private theorem c147968 : checkChunk 147968 128 = true := by decide +kernel
private theorem c148096 : checkChunk 148096 128 = true := by decide +kernel
private theorem c148224 : checkChunk 148224 128 = true := by decide +kernel
private theorem c148352 : checkChunk 148352 128 = true := by decide +kernel
private theorem c148480 : checkChunk 148480 128 = true := by decide +kernel
private theorem c148608 : checkChunk 148608 128 = true := by decide +kernel
private theorem c148736 : checkChunk 148736 128 = true := by decide +kernel
private theorem c148864 : checkChunk 148864 128 = true := by decide +kernel
private theorem c148992 : checkChunk 148992 128 = true := by decide +kernel
private theorem c149120 : checkChunk 149120 128 = true := by decide +kernel
private theorem c149248 : checkChunk 149248 128 = true := by decide +kernel
private theorem c149376 : checkChunk 149376 128 = true := by decide +kernel
private theorem c149504 : checkChunk 149504 128 = true := by decide +kernel
private theorem c149632 : checkChunk 149632 128 = true := by decide +kernel
private theorem c149760 : checkChunk 149760 128 = true := by decide +kernel
private theorem c149888 : checkChunk 149888 128 = true := by decide +kernel
private theorem c150016 : checkChunk 150016 128 = true := by decide +kernel
private theorem c150144 : checkChunk 150144 128 = true := by decide +kernel
private theorem c150272 : checkChunk 150272 128 = true := by decide +kernel
private theorem c150400 : checkChunk 150400 128 = true := by decide +kernel
private theorem c150528 : checkChunk 150528 128 = true := by decide +kernel
private theorem c150656 : checkChunk 150656 128 = true := by decide +kernel
private theorem c150784 : checkChunk 150784 128 = true := by decide +kernel
private theorem c150912 : checkChunk 150912 128 = true := by decide +kernel
private theorem c151040 : checkChunk 151040 128 = true := by decide +kernel
private theorem c151168 : checkChunk 151168 128 = true := by decide +kernel
private theorem c151296 : checkChunk 151296 128 = true := by decide +kernel
private theorem c151424 : checkChunk 151424 128 = true := by decide +kernel
private theorem c151552 : checkChunk 151552 128 = true := by decide +kernel
private theorem c151680 : checkChunk 151680 128 = true := by decide +kernel
private theorem c151808 : checkChunk 151808 128 = true := by decide +kernel
private theorem c151936 : checkChunk 151936 128 = true := by decide +kernel
private theorem c152064 : checkChunk 152064 128 = true := by decide +kernel
private theorem c152192 : checkChunk 152192 128 = true := by decide +kernel
private theorem c152320 : checkChunk 152320 128 = true := by decide +kernel
private theorem c152448 : checkChunk 152448 128 = true := by decide +kernel
private theorem c152576 : checkChunk 152576 128 = true := by decide +kernel
private theorem c152704 : checkChunk 152704 128 = true := by decide +kernel
private theorem c152832 : checkChunk 152832 128 = true := by decide +kernel
private theorem c152960 : checkChunk 152960 128 = true := by decide +kernel
private theorem c153088 : checkChunk 153088 128 = true := by decide +kernel
private theorem c153216 : checkChunk 153216 128 = true := by decide +kernel
private theorem c153344 : checkChunk 153344 128 = true := by decide +kernel
private theorem c153472 : checkChunk 153472 128 = true := by decide +kernel
private theorem c153600 : checkChunk 153600 128 = true := by decide +kernel
private theorem c153728 : checkChunk 153728 128 = true := by decide +kernel
private theorem c153856 : checkChunk 153856 128 = true := by decide +kernel
private theorem c153984 : checkChunk 153984 128 = true := by decide +kernel
private theorem c154112 : checkChunk 154112 128 = true := by decide +kernel
private theorem c154240 : checkChunk 154240 128 = true := by decide +kernel
private theorem c154368 : checkChunk 154368 128 = true := by decide +kernel
private theorem c154496 : checkChunk 154496 128 = true := by decide +kernel
private theorem c154624 : checkChunk 154624 128 = true := by decide +kernel
private theorem c154752 : checkChunk 154752 128 = true := by decide +kernel
private theorem c154880 : checkChunk 154880 128 = true := by decide +kernel
private theorem c155008 : checkChunk 155008 128 = true := by decide +kernel
private theorem c155136 : checkChunk 155136 128 = true := by decide +kernel
private theorem c155264 : checkChunk 155264 128 = true := by decide +kernel
private theorem c155392 : checkChunk 155392 128 = true := by decide +kernel
private theorem c155520 : checkChunk 155520 128 = true := by decide +kernel

public theorem checked : Checked 147456 155648 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 147456 128 c147456) (checkChunk_sound 147584 128 c147584)) (Checked.append (checkChunk_sound 147712 128 c147712) (checkChunk_sound 147840 128 c147840))) (Checked.append (Checked.append (checkChunk_sound 147968 128 c147968) (checkChunk_sound 148096 128 c148096)) (Checked.append (checkChunk_sound 148224 128 c148224) (checkChunk_sound 148352 128 c148352)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 148480 128 c148480) (checkChunk_sound 148608 128 c148608)) (Checked.append (checkChunk_sound 148736 128 c148736) (checkChunk_sound 148864 128 c148864))) (Checked.append (Checked.append (checkChunk_sound 148992 128 c148992) (checkChunk_sound 149120 128 c149120)) (Checked.append (checkChunk_sound 149248 128 c149248) (checkChunk_sound 149376 128 c149376))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 149504 128 c149504) (checkChunk_sound 149632 128 c149632)) (Checked.append (checkChunk_sound 149760 128 c149760) (checkChunk_sound 149888 128 c149888))) (Checked.append (Checked.append (checkChunk_sound 150016 128 c150016) (checkChunk_sound 150144 128 c150144)) (Checked.append (checkChunk_sound 150272 128 c150272) (checkChunk_sound 150400 128 c150400)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 150528 128 c150528) (checkChunk_sound 150656 128 c150656)) (Checked.append (checkChunk_sound 150784 128 c150784) (checkChunk_sound 150912 128 c150912))) (Checked.append (Checked.append (checkChunk_sound 151040 128 c151040) (checkChunk_sound 151168 128 c151168)) (Checked.append (checkChunk_sound 151296 128 c151296) (checkChunk_sound 151424 128 c151424)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 151552 128 c151552) (checkChunk_sound 151680 128 c151680)) (Checked.append (checkChunk_sound 151808 128 c151808) (checkChunk_sound 151936 128 c151936))) (Checked.append (Checked.append (checkChunk_sound 152064 128 c152064) (checkChunk_sound 152192 128 c152192)) (Checked.append (checkChunk_sound 152320 128 c152320) (checkChunk_sound 152448 128 c152448)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 152576 128 c152576) (checkChunk_sound 152704 128 c152704)) (Checked.append (checkChunk_sound 152832 128 c152832) (checkChunk_sound 152960 128 c152960))) (Checked.append (Checked.append (checkChunk_sound 153088 128 c153088) (checkChunk_sound 153216 128 c153216)) (Checked.append (checkChunk_sound 153344 128 c153344) (checkChunk_sound 153472 128 c153472))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 153600 128 c153600) (checkChunk_sound 153728 128 c153728)) (Checked.append (checkChunk_sound 153856 128 c153856) (checkChunk_sound 153984 128 c153984))) (Checked.append (Checked.append (checkChunk_sound 154112 128 c154112) (checkChunk_sound 154240 128 c154240)) (Checked.append (checkChunk_sound 154368 128 c154368) (checkChunk_sound 154496 128 c154496)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 154624 128 c154624) (checkChunk_sound 154752 128 c154752)) (Checked.append (checkChunk_sound 154880 128 c154880) (checkChunk_sound 155008 128 c155008))) (Checked.append (Checked.append (checkChunk_sound 155136 128 c155136) (checkChunk_sound 155264 128 c155264)) (Checked.append (checkChunk_sound 155392 128 c155392) (checkChunk_sound 155520 128 c155520)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B017
