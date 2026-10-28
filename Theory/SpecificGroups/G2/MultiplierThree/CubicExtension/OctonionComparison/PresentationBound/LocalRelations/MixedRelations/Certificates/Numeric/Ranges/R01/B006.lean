module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [270336, 278528).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B006
private theorem c270336 : checkChunk 270336 128 = true := by decide +kernel
private theorem c270464 : checkChunk 270464 128 = true := by decide +kernel
private theorem c270592 : checkChunk 270592 128 = true := by decide +kernel
private theorem c270720 : checkChunk 270720 128 = true := by decide +kernel
private theorem c270848 : checkChunk 270848 128 = true := by decide +kernel
private theorem c270976 : checkChunk 270976 128 = true := by decide +kernel
private theorem c271104 : checkChunk 271104 128 = true := by decide +kernel
private theorem c271232 : checkChunk 271232 128 = true := by decide +kernel
private theorem c271360 : checkChunk 271360 128 = true := by decide +kernel
private theorem c271488 : checkChunk 271488 128 = true := by decide +kernel
private theorem c271616 : checkChunk 271616 128 = true := by decide +kernel
private theorem c271744 : checkChunk 271744 128 = true := by decide +kernel
private theorem c271872 : checkChunk 271872 128 = true := by decide +kernel
private theorem c272000 : checkChunk 272000 128 = true := by decide +kernel
private theorem c272128 : checkChunk 272128 128 = true := by decide +kernel
private theorem c272256 : checkChunk 272256 128 = true := by decide +kernel
private theorem c272384 : checkChunk 272384 128 = true := by decide +kernel
private theorem c272512 : checkChunk 272512 128 = true := by decide +kernel
private theorem c272640 : checkChunk 272640 128 = true := by decide +kernel
private theorem c272768 : checkChunk 272768 128 = true := by decide +kernel
private theorem c272896 : checkChunk 272896 128 = true := by decide +kernel
private theorem c273024 : checkChunk 273024 128 = true := by decide +kernel
private theorem c273152 : checkChunk 273152 128 = true := by decide +kernel
private theorem c273280 : checkChunk 273280 128 = true := by decide +kernel
private theorem c273408 : checkChunk 273408 128 = true := by decide +kernel
private theorem c273536 : checkChunk 273536 128 = true := by decide +kernel
private theorem c273664 : checkChunk 273664 128 = true := by decide +kernel
private theorem c273792 : checkChunk 273792 128 = true := by decide +kernel
private theorem c273920 : checkChunk 273920 128 = true := by decide +kernel
private theorem c274048 : checkChunk 274048 128 = true := by decide +kernel
private theorem c274176 : checkChunk 274176 128 = true := by decide +kernel
private theorem c274304 : checkChunk 274304 128 = true := by decide +kernel
private theorem c274432 : checkChunk 274432 128 = true := by decide +kernel
private theorem c274560 : checkChunk 274560 128 = true := by decide +kernel
private theorem c274688 : checkChunk 274688 128 = true := by decide +kernel
private theorem c274816 : checkChunk 274816 128 = true := by decide +kernel
private theorem c274944 : checkChunk 274944 128 = true := by decide +kernel
private theorem c275072 : checkChunk 275072 128 = true := by decide +kernel
private theorem c275200 : checkChunk 275200 128 = true := by decide +kernel
private theorem c275328 : checkChunk 275328 128 = true := by decide +kernel
private theorem c275456 : checkChunk 275456 128 = true := by decide +kernel
private theorem c275584 : checkChunk 275584 128 = true := by decide +kernel
private theorem c275712 : checkChunk 275712 128 = true := by decide +kernel
private theorem c275840 : checkChunk 275840 128 = true := by decide +kernel
private theorem c275968 : checkChunk 275968 128 = true := by decide +kernel
private theorem c276096 : checkChunk 276096 128 = true := by decide +kernel
private theorem c276224 : checkChunk 276224 128 = true := by decide +kernel
private theorem c276352 : checkChunk 276352 128 = true := by decide +kernel
private theorem c276480 : checkChunk 276480 128 = true := by decide +kernel
private theorem c276608 : checkChunk 276608 128 = true := by decide +kernel
private theorem c276736 : checkChunk 276736 128 = true := by decide +kernel
private theorem c276864 : checkChunk 276864 128 = true := by decide +kernel
private theorem c276992 : checkChunk 276992 128 = true := by decide +kernel
private theorem c277120 : checkChunk 277120 128 = true := by decide +kernel
private theorem c277248 : checkChunk 277248 128 = true := by decide +kernel
private theorem c277376 : checkChunk 277376 128 = true := by decide +kernel
private theorem c277504 : checkChunk 277504 128 = true := by decide +kernel
private theorem c277632 : checkChunk 277632 128 = true := by decide +kernel
private theorem c277760 : checkChunk 277760 128 = true := by decide +kernel
private theorem c277888 : checkChunk 277888 128 = true := by decide +kernel
private theorem c278016 : checkChunk 278016 128 = true := by decide +kernel
private theorem c278144 : checkChunk 278144 128 = true := by decide +kernel
private theorem c278272 : checkChunk 278272 128 = true := by decide +kernel
private theorem c278400 : checkChunk 278400 128 = true := by decide +kernel

public theorem checked : Checked 270336 278528 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 270336 128 c270336) (checkChunk_sound 270464 128 c270464)) (Checked.append (checkChunk_sound 270592 128 c270592) (checkChunk_sound 270720 128 c270720))) (Checked.append (Checked.append (checkChunk_sound 270848 128 c270848) (checkChunk_sound 270976 128 c270976)) (Checked.append (checkChunk_sound 271104 128 c271104) (checkChunk_sound 271232 128 c271232)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 271360 128 c271360) (checkChunk_sound 271488 128 c271488)) (Checked.append (checkChunk_sound 271616 128 c271616) (checkChunk_sound 271744 128 c271744))) (Checked.append (Checked.append (checkChunk_sound 271872 128 c271872) (checkChunk_sound 272000 128 c272000)) (Checked.append (checkChunk_sound 272128 128 c272128) (checkChunk_sound 272256 128 c272256))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 272384 128 c272384) (checkChunk_sound 272512 128 c272512)) (Checked.append (checkChunk_sound 272640 128 c272640) (checkChunk_sound 272768 128 c272768))) (Checked.append (Checked.append (checkChunk_sound 272896 128 c272896) (checkChunk_sound 273024 128 c273024)) (Checked.append (checkChunk_sound 273152 128 c273152) (checkChunk_sound 273280 128 c273280)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 273408 128 c273408) (checkChunk_sound 273536 128 c273536)) (Checked.append (checkChunk_sound 273664 128 c273664) (checkChunk_sound 273792 128 c273792))) (Checked.append (Checked.append (checkChunk_sound 273920 128 c273920) (checkChunk_sound 274048 128 c274048)) (Checked.append (checkChunk_sound 274176 128 c274176) (checkChunk_sound 274304 128 c274304)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 274432 128 c274432) (checkChunk_sound 274560 128 c274560)) (Checked.append (checkChunk_sound 274688 128 c274688) (checkChunk_sound 274816 128 c274816))) (Checked.append (Checked.append (checkChunk_sound 274944 128 c274944) (checkChunk_sound 275072 128 c275072)) (Checked.append (checkChunk_sound 275200 128 c275200) (checkChunk_sound 275328 128 c275328)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 275456 128 c275456) (checkChunk_sound 275584 128 c275584)) (Checked.append (checkChunk_sound 275712 128 c275712) (checkChunk_sound 275840 128 c275840))) (Checked.append (Checked.append (checkChunk_sound 275968 128 c275968) (checkChunk_sound 276096 128 c276096)) (Checked.append (checkChunk_sound 276224 128 c276224) (checkChunk_sound 276352 128 c276352))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 276480 128 c276480) (checkChunk_sound 276608 128 c276608)) (Checked.append (checkChunk_sound 276736 128 c276736) (checkChunk_sound 276864 128 c276864))) (Checked.append (Checked.append (checkChunk_sound 276992 128 c276992) (checkChunk_sound 277120 128 c277120)) (Checked.append (checkChunk_sound 277248 128 c277248) (checkChunk_sound 277376 128 c277376)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 277504 128 c277504) (checkChunk_sound 277632 128 c277632)) (Checked.append (checkChunk_sound 277760 128 c277760) (checkChunk_sound 277888 128 c277888))) (Checked.append (Checked.append (checkChunk_sound 278016 128 c278016) (checkChunk_sound 278144 128 c278144)) (Checked.append (checkChunk_sound 278272 128 c278272) (checkChunk_sound 278400 128 c278400)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B006
