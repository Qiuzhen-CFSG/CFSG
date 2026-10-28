module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [983040, 991232).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B015
private theorem c983040 : checkChunk 983040 128 = true := by decide +kernel
private theorem c983168 : checkChunk 983168 128 = true := by decide +kernel
private theorem c983296 : checkChunk 983296 128 = true := by decide +kernel
private theorem c983424 : checkChunk 983424 128 = true := by decide +kernel
private theorem c983552 : checkChunk 983552 128 = true := by decide +kernel
private theorem c983680 : checkChunk 983680 128 = true := by decide +kernel
private theorem c983808 : checkChunk 983808 128 = true := by decide +kernel
private theorem c983936 : checkChunk 983936 128 = true := by decide +kernel
private theorem c984064 : checkChunk 984064 128 = true := by decide +kernel
private theorem c984192 : checkChunk 984192 128 = true := by decide +kernel
private theorem c984320 : checkChunk 984320 128 = true := by decide +kernel
private theorem c984448 : checkChunk 984448 128 = true := by decide +kernel
private theorem c984576 : checkChunk 984576 128 = true := by decide +kernel
private theorem c984704 : checkChunk 984704 128 = true := by decide +kernel
private theorem c984832 : checkChunk 984832 128 = true := by decide +kernel
private theorem c984960 : checkChunk 984960 128 = true := by decide +kernel
private theorem c985088 : checkChunk 985088 128 = true := by decide +kernel
private theorem c985216 : checkChunk 985216 128 = true := by decide +kernel
private theorem c985344 : checkChunk 985344 128 = true := by decide +kernel
private theorem c985472 : checkChunk 985472 128 = true := by decide +kernel
private theorem c985600 : checkChunk 985600 128 = true := by decide +kernel
private theorem c985728 : checkChunk 985728 128 = true := by decide +kernel
private theorem c985856 : checkChunk 985856 128 = true := by decide +kernel
private theorem c985984 : checkChunk 985984 128 = true := by decide +kernel
private theorem c986112 : checkChunk 986112 128 = true := by decide +kernel
private theorem c986240 : checkChunk 986240 128 = true := by decide +kernel
private theorem c986368 : checkChunk 986368 128 = true := by decide +kernel
private theorem c986496 : checkChunk 986496 128 = true := by decide +kernel
private theorem c986624 : checkChunk 986624 128 = true := by decide +kernel
private theorem c986752 : checkChunk 986752 128 = true := by decide +kernel
private theorem c986880 : checkChunk 986880 128 = true := by decide +kernel
private theorem c987008 : checkChunk 987008 128 = true := by decide +kernel
private theorem c987136 : checkChunk 987136 128 = true := by decide +kernel
private theorem c987264 : checkChunk 987264 128 = true := by decide +kernel
private theorem c987392 : checkChunk 987392 128 = true := by decide +kernel
private theorem c987520 : checkChunk 987520 128 = true := by decide +kernel
private theorem c987648 : checkChunk 987648 128 = true := by decide +kernel
private theorem c987776 : checkChunk 987776 128 = true := by decide +kernel
private theorem c987904 : checkChunk 987904 128 = true := by decide +kernel
private theorem c988032 : checkChunk 988032 128 = true := by decide +kernel
private theorem c988160 : checkChunk 988160 128 = true := by decide +kernel
private theorem c988288 : checkChunk 988288 128 = true := by decide +kernel
private theorem c988416 : checkChunk 988416 128 = true := by decide +kernel
private theorem c988544 : checkChunk 988544 128 = true := by decide +kernel
private theorem c988672 : checkChunk 988672 128 = true := by decide +kernel
private theorem c988800 : checkChunk 988800 128 = true := by decide +kernel
private theorem c988928 : checkChunk 988928 128 = true := by decide +kernel
private theorem c989056 : checkChunk 989056 128 = true := by decide +kernel
private theorem c989184 : checkChunk 989184 128 = true := by decide +kernel
private theorem c989312 : checkChunk 989312 128 = true := by decide +kernel
private theorem c989440 : checkChunk 989440 128 = true := by decide +kernel
private theorem c989568 : checkChunk 989568 128 = true := by decide +kernel
private theorem c989696 : checkChunk 989696 128 = true := by decide +kernel
private theorem c989824 : checkChunk 989824 128 = true := by decide +kernel
private theorem c989952 : checkChunk 989952 128 = true := by decide +kernel
private theorem c990080 : checkChunk 990080 128 = true := by decide +kernel
private theorem c990208 : checkChunk 990208 128 = true := by decide +kernel
private theorem c990336 : checkChunk 990336 128 = true := by decide +kernel
private theorem c990464 : checkChunk 990464 128 = true := by decide +kernel
private theorem c990592 : checkChunk 990592 128 = true := by decide +kernel
private theorem c990720 : checkChunk 990720 128 = true := by decide +kernel
private theorem c990848 : checkChunk 990848 128 = true := by decide +kernel
private theorem c990976 : checkChunk 990976 128 = true := by decide +kernel
private theorem c991104 : checkChunk 991104 128 = true := by decide +kernel

public theorem checked : Checked 983040 991232 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 983040 128 c983040) (checkChunk_sound 983168 128 c983168)) (Checked.append (checkChunk_sound 983296 128 c983296) (checkChunk_sound 983424 128 c983424))) (Checked.append (Checked.append (checkChunk_sound 983552 128 c983552) (checkChunk_sound 983680 128 c983680)) (Checked.append (checkChunk_sound 983808 128 c983808) (checkChunk_sound 983936 128 c983936)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 984064 128 c984064) (checkChunk_sound 984192 128 c984192)) (Checked.append (checkChunk_sound 984320 128 c984320) (checkChunk_sound 984448 128 c984448))) (Checked.append (Checked.append (checkChunk_sound 984576 128 c984576) (checkChunk_sound 984704 128 c984704)) (Checked.append (checkChunk_sound 984832 128 c984832) (checkChunk_sound 984960 128 c984960))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 985088 128 c985088) (checkChunk_sound 985216 128 c985216)) (Checked.append (checkChunk_sound 985344 128 c985344) (checkChunk_sound 985472 128 c985472))) (Checked.append (Checked.append (checkChunk_sound 985600 128 c985600) (checkChunk_sound 985728 128 c985728)) (Checked.append (checkChunk_sound 985856 128 c985856) (checkChunk_sound 985984 128 c985984)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 986112 128 c986112) (checkChunk_sound 986240 128 c986240)) (Checked.append (checkChunk_sound 986368 128 c986368) (checkChunk_sound 986496 128 c986496))) (Checked.append (Checked.append (checkChunk_sound 986624 128 c986624) (checkChunk_sound 986752 128 c986752)) (Checked.append (checkChunk_sound 986880 128 c986880) (checkChunk_sound 987008 128 c987008)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 987136 128 c987136) (checkChunk_sound 987264 128 c987264)) (Checked.append (checkChunk_sound 987392 128 c987392) (checkChunk_sound 987520 128 c987520))) (Checked.append (Checked.append (checkChunk_sound 987648 128 c987648) (checkChunk_sound 987776 128 c987776)) (Checked.append (checkChunk_sound 987904 128 c987904) (checkChunk_sound 988032 128 c988032)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 988160 128 c988160) (checkChunk_sound 988288 128 c988288)) (Checked.append (checkChunk_sound 988416 128 c988416) (checkChunk_sound 988544 128 c988544))) (Checked.append (Checked.append (checkChunk_sound 988672 128 c988672) (checkChunk_sound 988800 128 c988800)) (Checked.append (checkChunk_sound 988928 128 c988928) (checkChunk_sound 989056 128 c989056))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 989184 128 c989184) (checkChunk_sound 989312 128 c989312)) (Checked.append (checkChunk_sound 989440 128 c989440) (checkChunk_sound 989568 128 c989568))) (Checked.append (Checked.append (checkChunk_sound 989696 128 c989696) (checkChunk_sound 989824 128 c989824)) (Checked.append (checkChunk_sound 989952 128 c989952) (checkChunk_sound 990080 128 c990080)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 990208 128 c990208) (checkChunk_sound 990336 128 c990336)) (Checked.append (checkChunk_sound 990464 128 c990464) (checkChunk_sound 990592 128 c990592))) (Checked.append (Checked.append (checkChunk_sound 990720 128 c990720) (checkChunk_sound 990848 128 c990848)) (Checked.append (checkChunk_sound 990976 128 c990976) (checkChunk_sound 991104 128 c991104)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B015
