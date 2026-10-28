module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [81920, 90112).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B009
private theorem c81920 : checkChunk 81920 128 = true := by decide +kernel
private theorem c82048 : checkChunk 82048 128 = true := by decide +kernel
private theorem c82176 : checkChunk 82176 128 = true := by decide +kernel
private theorem c82304 : checkChunk 82304 128 = true := by decide +kernel
private theorem c82432 : checkChunk 82432 128 = true := by decide +kernel
private theorem c82560 : checkChunk 82560 128 = true := by decide +kernel
private theorem c82688 : checkChunk 82688 128 = true := by decide +kernel
private theorem c82816 : checkChunk 82816 128 = true := by decide +kernel
private theorem c82944 : checkChunk 82944 128 = true := by decide +kernel
private theorem c83072 : checkChunk 83072 128 = true := by decide +kernel
private theorem c83200 : checkChunk 83200 128 = true := by decide +kernel
private theorem c83328 : checkChunk 83328 128 = true := by decide +kernel
private theorem c83456 : checkChunk 83456 128 = true := by decide +kernel
private theorem c83584 : checkChunk 83584 128 = true := by decide +kernel
private theorem c83712 : checkChunk 83712 128 = true := by decide +kernel
private theorem c83840 : checkChunk 83840 128 = true := by decide +kernel
private theorem c83968 : checkChunk 83968 128 = true := by decide +kernel
private theorem c84096 : checkChunk 84096 128 = true := by decide +kernel
private theorem c84224 : checkChunk 84224 128 = true := by decide +kernel
private theorem c84352 : checkChunk 84352 128 = true := by decide +kernel
private theorem c84480 : checkChunk 84480 128 = true := by decide +kernel
private theorem c84608 : checkChunk 84608 128 = true := by decide +kernel
private theorem c84736 : checkChunk 84736 128 = true := by decide +kernel
private theorem c84864 : checkChunk 84864 128 = true := by decide +kernel
private theorem c84992 : checkChunk 84992 128 = true := by decide +kernel
private theorem c85120 : checkChunk 85120 128 = true := by decide +kernel
private theorem c85248 : checkChunk 85248 128 = true := by decide +kernel
private theorem c85376 : checkChunk 85376 128 = true := by decide +kernel
private theorem c85504 : checkChunk 85504 128 = true := by decide +kernel
private theorem c85632 : checkChunk 85632 128 = true := by decide +kernel
private theorem c85760 : checkChunk 85760 128 = true := by decide +kernel
private theorem c85888 : checkChunk 85888 128 = true := by decide +kernel
private theorem c86016 : checkChunk 86016 128 = true := by decide +kernel
private theorem c86144 : checkChunk 86144 128 = true := by decide +kernel
private theorem c86272 : checkChunk 86272 128 = true := by decide +kernel
private theorem c86400 : checkChunk 86400 128 = true := by decide +kernel
private theorem c86528 : checkChunk 86528 128 = true := by decide +kernel
private theorem c86656 : checkChunk 86656 128 = true := by decide +kernel
private theorem c86784 : checkChunk 86784 128 = true := by decide +kernel
private theorem c86912 : checkChunk 86912 128 = true := by decide +kernel
private theorem c87040 : checkChunk 87040 128 = true := by decide +kernel
private theorem c87168 : checkChunk 87168 128 = true := by decide +kernel
private theorem c87296 : checkChunk 87296 128 = true := by decide +kernel
private theorem c87424 : checkChunk 87424 128 = true := by decide +kernel
private theorem c87552 : checkChunk 87552 128 = true := by decide +kernel
private theorem c87680 : checkChunk 87680 128 = true := by decide +kernel
private theorem c87808 : checkChunk 87808 128 = true := by decide +kernel
private theorem c87936 : checkChunk 87936 128 = true := by decide +kernel
private theorem c88064 : checkChunk 88064 128 = true := by decide +kernel
private theorem c88192 : checkChunk 88192 128 = true := by decide +kernel
private theorem c88320 : checkChunk 88320 128 = true := by decide +kernel
private theorem c88448 : checkChunk 88448 128 = true := by decide +kernel
private theorem c88576 : checkChunk 88576 128 = true := by decide +kernel
private theorem c88704 : checkChunk 88704 128 = true := by decide +kernel
private theorem c88832 : checkChunk 88832 128 = true := by decide +kernel
private theorem c88960 : checkChunk 88960 128 = true := by decide +kernel
private theorem c89088 : checkChunk 89088 128 = true := by decide +kernel
private theorem c89216 : checkChunk 89216 128 = true := by decide +kernel
private theorem c89344 : checkChunk 89344 128 = true := by decide +kernel
private theorem c89472 : checkChunk 89472 128 = true := by decide +kernel
private theorem c89600 : checkChunk 89600 128 = true := by decide +kernel
private theorem c89728 : checkChunk 89728 128 = true := by decide +kernel
private theorem c89856 : checkChunk 89856 128 = true := by decide +kernel
private theorem c89984 : checkChunk 89984 128 = true := by decide +kernel

public theorem checked : Checked 81920 90112 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 81920 128 c81920) (checkChunk_sound 82048 128 c82048)) (Checked.append (checkChunk_sound 82176 128 c82176) (checkChunk_sound 82304 128 c82304))) (Checked.append (Checked.append (checkChunk_sound 82432 128 c82432) (checkChunk_sound 82560 128 c82560)) (Checked.append (checkChunk_sound 82688 128 c82688) (checkChunk_sound 82816 128 c82816)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 82944 128 c82944) (checkChunk_sound 83072 128 c83072)) (Checked.append (checkChunk_sound 83200 128 c83200) (checkChunk_sound 83328 128 c83328))) (Checked.append (Checked.append (checkChunk_sound 83456 128 c83456) (checkChunk_sound 83584 128 c83584)) (Checked.append (checkChunk_sound 83712 128 c83712) (checkChunk_sound 83840 128 c83840))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 83968 128 c83968) (checkChunk_sound 84096 128 c84096)) (Checked.append (checkChunk_sound 84224 128 c84224) (checkChunk_sound 84352 128 c84352))) (Checked.append (Checked.append (checkChunk_sound 84480 128 c84480) (checkChunk_sound 84608 128 c84608)) (Checked.append (checkChunk_sound 84736 128 c84736) (checkChunk_sound 84864 128 c84864)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 84992 128 c84992) (checkChunk_sound 85120 128 c85120)) (Checked.append (checkChunk_sound 85248 128 c85248) (checkChunk_sound 85376 128 c85376))) (Checked.append (Checked.append (checkChunk_sound 85504 128 c85504) (checkChunk_sound 85632 128 c85632)) (Checked.append (checkChunk_sound 85760 128 c85760) (checkChunk_sound 85888 128 c85888)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 86016 128 c86016) (checkChunk_sound 86144 128 c86144)) (Checked.append (checkChunk_sound 86272 128 c86272) (checkChunk_sound 86400 128 c86400))) (Checked.append (Checked.append (checkChunk_sound 86528 128 c86528) (checkChunk_sound 86656 128 c86656)) (Checked.append (checkChunk_sound 86784 128 c86784) (checkChunk_sound 86912 128 c86912)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 87040 128 c87040) (checkChunk_sound 87168 128 c87168)) (Checked.append (checkChunk_sound 87296 128 c87296) (checkChunk_sound 87424 128 c87424))) (Checked.append (Checked.append (checkChunk_sound 87552 128 c87552) (checkChunk_sound 87680 128 c87680)) (Checked.append (checkChunk_sound 87808 128 c87808) (checkChunk_sound 87936 128 c87936))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 88064 128 c88064) (checkChunk_sound 88192 128 c88192)) (Checked.append (checkChunk_sound 88320 128 c88320) (checkChunk_sound 88448 128 c88448))) (Checked.append (Checked.append (checkChunk_sound 88576 128 c88576) (checkChunk_sound 88704 128 c88704)) (Checked.append (checkChunk_sound 88832 128 c88832) (checkChunk_sound 88960 128 c88960)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 89088 128 c89088) (checkChunk_sound 89216 128 c89216)) (Checked.append (checkChunk_sound 89344 128 c89344) (checkChunk_sound 89472 128 c89472))) (Checked.append (Checked.append (checkChunk_sound 89600 128 c89600) (checkChunk_sound 89728 128 c89728)) (Checked.append (checkChunk_sound 89856 128 c89856) (checkChunk_sound 89984 128 c89984)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B009
