module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [49152, 57344).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B005
private theorem c49152 : checkChunk 49152 128 = true := by decide +kernel
private theorem c49280 : checkChunk 49280 128 = true := by decide +kernel
private theorem c49408 : checkChunk 49408 128 = true := by decide +kernel
private theorem c49536 : checkChunk 49536 128 = true := by decide +kernel
private theorem c49664 : checkChunk 49664 128 = true := by decide +kernel
private theorem c49792 : checkChunk 49792 128 = true := by decide +kernel
private theorem c49920 : checkChunk 49920 128 = true := by decide +kernel
private theorem c50048 : checkChunk 50048 128 = true := by decide +kernel
private theorem c50176 : checkChunk 50176 128 = true := by decide +kernel
private theorem c50304 : checkChunk 50304 128 = true := by decide +kernel
private theorem c50432 : checkChunk 50432 128 = true := by decide +kernel
private theorem c50560 : checkChunk 50560 128 = true := by decide +kernel
private theorem c50688 : checkChunk 50688 128 = true := by decide +kernel
private theorem c50816 : checkChunk 50816 128 = true := by decide +kernel
private theorem c50944 : checkChunk 50944 128 = true := by decide +kernel
private theorem c51072 : checkChunk 51072 128 = true := by decide +kernel
private theorem c51200 : checkChunk 51200 128 = true := by decide +kernel
private theorem c51328 : checkChunk 51328 128 = true := by decide +kernel
private theorem c51456 : checkChunk 51456 128 = true := by decide +kernel
private theorem c51584 : checkChunk 51584 128 = true := by decide +kernel
private theorem c51712 : checkChunk 51712 128 = true := by decide +kernel
private theorem c51840 : checkChunk 51840 128 = true := by decide +kernel
private theorem c51968 : checkChunk 51968 128 = true := by decide +kernel
private theorem c52096 : checkChunk 52096 128 = true := by decide +kernel
private theorem c52224 : checkChunk 52224 128 = true := by decide +kernel
private theorem c52352 : checkChunk 52352 128 = true := by decide +kernel
private theorem c52480 : checkChunk 52480 128 = true := by decide +kernel
private theorem c52608 : checkChunk 52608 128 = true := by decide +kernel
private theorem c52736 : checkChunk 52736 128 = true := by decide +kernel
private theorem c52864 : checkChunk 52864 128 = true := by decide +kernel
private theorem c52992 : checkChunk 52992 128 = true := by decide +kernel
private theorem c53120 : checkChunk 53120 128 = true := by decide +kernel
private theorem c53248 : checkChunk 53248 128 = true := by decide +kernel
private theorem c53376 : checkChunk 53376 128 = true := by decide +kernel
private theorem c53504 : checkChunk 53504 128 = true := by decide +kernel
private theorem c53632 : checkChunk 53632 128 = true := by decide +kernel
private theorem c53760 : checkChunk 53760 128 = true := by decide +kernel
private theorem c53888 : checkChunk 53888 128 = true := by decide +kernel
private theorem c54016 : checkChunk 54016 128 = true := by decide +kernel
private theorem c54144 : checkChunk 54144 128 = true := by decide +kernel
private theorem c54272 : checkChunk 54272 128 = true := by decide +kernel
private theorem c54400 : checkChunk 54400 128 = true := by decide +kernel
private theorem c54528 : checkChunk 54528 128 = true := by decide +kernel
private theorem c54656 : checkChunk 54656 128 = true := by decide +kernel
private theorem c54784 : checkChunk 54784 128 = true := by decide +kernel
private theorem c54912 : checkChunk 54912 128 = true := by decide +kernel
private theorem c55040 : checkChunk 55040 128 = true := by decide +kernel
private theorem c55168 : checkChunk 55168 128 = true := by decide +kernel
private theorem c55296 : checkChunk 55296 128 = true := by decide +kernel
private theorem c55424 : checkChunk 55424 128 = true := by decide +kernel
private theorem c55552 : checkChunk 55552 128 = true := by decide +kernel
private theorem c55680 : checkChunk 55680 128 = true := by decide +kernel
private theorem c55808 : checkChunk 55808 128 = true := by decide +kernel
private theorem c55936 : checkChunk 55936 128 = true := by decide +kernel
private theorem c56064 : checkChunk 56064 128 = true := by decide +kernel
private theorem c56192 : checkChunk 56192 128 = true := by decide +kernel
private theorem c56320 : checkChunk 56320 128 = true := by decide +kernel
private theorem c56448 : checkChunk 56448 128 = true := by decide +kernel
private theorem c56576 : checkChunk 56576 128 = true := by decide +kernel
private theorem c56704 : checkChunk 56704 128 = true := by decide +kernel
private theorem c56832 : checkChunk 56832 128 = true := by decide +kernel
private theorem c56960 : checkChunk 56960 128 = true := by decide +kernel
private theorem c57088 : checkChunk 57088 128 = true := by decide +kernel
private theorem c57216 : checkChunk 57216 128 = true := by decide +kernel

public theorem checked : Checked 49152 57344 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 49152 128 c49152) (checkChunk_sound 49280 128 c49280)) (Checked.append (checkChunk_sound 49408 128 c49408) (checkChunk_sound 49536 128 c49536))) (Checked.append (Checked.append (checkChunk_sound 49664 128 c49664) (checkChunk_sound 49792 128 c49792)) (Checked.append (checkChunk_sound 49920 128 c49920) (checkChunk_sound 50048 128 c50048)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 50176 128 c50176) (checkChunk_sound 50304 128 c50304)) (Checked.append (checkChunk_sound 50432 128 c50432) (checkChunk_sound 50560 128 c50560))) (Checked.append (Checked.append (checkChunk_sound 50688 128 c50688) (checkChunk_sound 50816 128 c50816)) (Checked.append (checkChunk_sound 50944 128 c50944) (checkChunk_sound 51072 128 c51072))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 51200 128 c51200) (checkChunk_sound 51328 128 c51328)) (Checked.append (checkChunk_sound 51456 128 c51456) (checkChunk_sound 51584 128 c51584))) (Checked.append (Checked.append (checkChunk_sound 51712 128 c51712) (checkChunk_sound 51840 128 c51840)) (Checked.append (checkChunk_sound 51968 128 c51968) (checkChunk_sound 52096 128 c52096)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 52224 128 c52224) (checkChunk_sound 52352 128 c52352)) (Checked.append (checkChunk_sound 52480 128 c52480) (checkChunk_sound 52608 128 c52608))) (Checked.append (Checked.append (checkChunk_sound 52736 128 c52736) (checkChunk_sound 52864 128 c52864)) (Checked.append (checkChunk_sound 52992 128 c52992) (checkChunk_sound 53120 128 c53120)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 53248 128 c53248) (checkChunk_sound 53376 128 c53376)) (Checked.append (checkChunk_sound 53504 128 c53504) (checkChunk_sound 53632 128 c53632))) (Checked.append (Checked.append (checkChunk_sound 53760 128 c53760) (checkChunk_sound 53888 128 c53888)) (Checked.append (checkChunk_sound 54016 128 c54016) (checkChunk_sound 54144 128 c54144)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 54272 128 c54272) (checkChunk_sound 54400 128 c54400)) (Checked.append (checkChunk_sound 54528 128 c54528) (checkChunk_sound 54656 128 c54656))) (Checked.append (Checked.append (checkChunk_sound 54784 128 c54784) (checkChunk_sound 54912 128 c54912)) (Checked.append (checkChunk_sound 55040 128 c55040) (checkChunk_sound 55168 128 c55168))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 55296 128 c55296) (checkChunk_sound 55424 128 c55424)) (Checked.append (checkChunk_sound 55552 128 c55552) (checkChunk_sound 55680 128 c55680))) (Checked.append (Checked.append (checkChunk_sound 55808 128 c55808) (checkChunk_sound 55936 128 c55936)) (Checked.append (checkChunk_sound 56064 128 c56064) (checkChunk_sound 56192 128 c56192)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 56320 128 c56320) (checkChunk_sound 56448 128 c56448)) (Checked.append (checkChunk_sound 56576 128 c56576) (checkChunk_sound 56704 128 c56704))) (Checked.append (Checked.append (checkChunk_sound 56832 128 c56832) (checkChunk_sound 56960 128 c56960)) (Checked.append (checkChunk_sound 57088 128 c57088) (checkChunk_sound 57216 128 c57216)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B005
