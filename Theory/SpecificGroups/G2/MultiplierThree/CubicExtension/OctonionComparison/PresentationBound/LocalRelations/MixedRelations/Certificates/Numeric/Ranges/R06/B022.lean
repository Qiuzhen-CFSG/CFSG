module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1466368, 1474560).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B022
private theorem c1466368 : checkChunk 1466368 128 = true := by decide +kernel
private theorem c1466496 : checkChunk 1466496 128 = true := by decide +kernel
private theorem c1466624 : checkChunk 1466624 128 = true := by decide +kernel
private theorem c1466752 : checkChunk 1466752 128 = true := by decide +kernel
private theorem c1466880 : checkChunk 1466880 128 = true := by decide +kernel
private theorem c1467008 : checkChunk 1467008 128 = true := by decide +kernel
private theorem c1467136 : checkChunk 1467136 128 = true := by decide +kernel
private theorem c1467264 : checkChunk 1467264 128 = true := by decide +kernel
private theorem c1467392 : checkChunk 1467392 128 = true := by decide +kernel
private theorem c1467520 : checkChunk 1467520 128 = true := by decide +kernel
private theorem c1467648 : checkChunk 1467648 128 = true := by decide +kernel
private theorem c1467776 : checkChunk 1467776 128 = true := by decide +kernel
private theorem c1467904 : checkChunk 1467904 128 = true := by decide +kernel
private theorem c1468032 : checkChunk 1468032 128 = true := by decide +kernel
private theorem c1468160 : checkChunk 1468160 128 = true := by decide +kernel
private theorem c1468288 : checkChunk 1468288 128 = true := by decide +kernel
private theorem c1468416 : checkChunk 1468416 128 = true := by decide +kernel
private theorem c1468544 : checkChunk 1468544 128 = true := by decide +kernel
private theorem c1468672 : checkChunk 1468672 128 = true := by decide +kernel
private theorem c1468800 : checkChunk 1468800 128 = true := by decide +kernel
private theorem c1468928 : checkChunk 1468928 128 = true := by decide +kernel
private theorem c1469056 : checkChunk 1469056 128 = true := by decide +kernel
private theorem c1469184 : checkChunk 1469184 128 = true := by decide +kernel
private theorem c1469312 : checkChunk 1469312 128 = true := by decide +kernel
private theorem c1469440 : checkChunk 1469440 128 = true := by decide +kernel
private theorem c1469568 : checkChunk 1469568 128 = true := by decide +kernel
private theorem c1469696 : checkChunk 1469696 128 = true := by decide +kernel
private theorem c1469824 : checkChunk 1469824 128 = true := by decide +kernel
private theorem c1469952 : checkChunk 1469952 128 = true := by decide +kernel
private theorem c1470080 : checkChunk 1470080 128 = true := by decide +kernel
private theorem c1470208 : checkChunk 1470208 128 = true := by decide +kernel
private theorem c1470336 : checkChunk 1470336 128 = true := by decide +kernel
private theorem c1470464 : checkChunk 1470464 128 = true := by decide +kernel
private theorem c1470592 : checkChunk 1470592 128 = true := by decide +kernel
private theorem c1470720 : checkChunk 1470720 128 = true := by decide +kernel
private theorem c1470848 : checkChunk 1470848 128 = true := by decide +kernel
private theorem c1470976 : checkChunk 1470976 128 = true := by decide +kernel
private theorem c1471104 : checkChunk 1471104 128 = true := by decide +kernel
private theorem c1471232 : checkChunk 1471232 128 = true := by decide +kernel
private theorem c1471360 : checkChunk 1471360 128 = true := by decide +kernel
private theorem c1471488 : checkChunk 1471488 128 = true := by decide +kernel
private theorem c1471616 : checkChunk 1471616 128 = true := by decide +kernel
private theorem c1471744 : checkChunk 1471744 128 = true := by decide +kernel
private theorem c1471872 : checkChunk 1471872 128 = true := by decide +kernel
private theorem c1472000 : checkChunk 1472000 128 = true := by decide +kernel
private theorem c1472128 : checkChunk 1472128 128 = true := by decide +kernel
private theorem c1472256 : checkChunk 1472256 128 = true := by decide +kernel
private theorem c1472384 : checkChunk 1472384 128 = true := by decide +kernel
private theorem c1472512 : checkChunk 1472512 128 = true := by decide +kernel
private theorem c1472640 : checkChunk 1472640 128 = true := by decide +kernel
private theorem c1472768 : checkChunk 1472768 128 = true := by decide +kernel
private theorem c1472896 : checkChunk 1472896 128 = true := by decide +kernel
private theorem c1473024 : checkChunk 1473024 128 = true := by decide +kernel
private theorem c1473152 : checkChunk 1473152 128 = true := by decide +kernel
private theorem c1473280 : checkChunk 1473280 128 = true := by decide +kernel
private theorem c1473408 : checkChunk 1473408 128 = true := by decide +kernel
private theorem c1473536 : checkChunk 1473536 128 = true := by decide +kernel
private theorem c1473664 : checkChunk 1473664 128 = true := by decide +kernel
private theorem c1473792 : checkChunk 1473792 128 = true := by decide +kernel
private theorem c1473920 : checkChunk 1473920 128 = true := by decide +kernel
private theorem c1474048 : checkChunk 1474048 128 = true := by decide +kernel
private theorem c1474176 : checkChunk 1474176 128 = true := by decide +kernel
private theorem c1474304 : checkChunk 1474304 128 = true := by decide +kernel
private theorem c1474432 : checkChunk 1474432 128 = true := by decide +kernel

public theorem checked : Checked 1466368 1474560 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1466368 128 c1466368) (checkChunk_sound 1466496 128 c1466496)) (Checked.append (checkChunk_sound 1466624 128 c1466624) (checkChunk_sound 1466752 128 c1466752))) (Checked.append (Checked.append (checkChunk_sound 1466880 128 c1466880) (checkChunk_sound 1467008 128 c1467008)) (Checked.append (checkChunk_sound 1467136 128 c1467136) (checkChunk_sound 1467264 128 c1467264)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1467392 128 c1467392) (checkChunk_sound 1467520 128 c1467520)) (Checked.append (checkChunk_sound 1467648 128 c1467648) (checkChunk_sound 1467776 128 c1467776))) (Checked.append (Checked.append (checkChunk_sound 1467904 128 c1467904) (checkChunk_sound 1468032 128 c1468032)) (Checked.append (checkChunk_sound 1468160 128 c1468160) (checkChunk_sound 1468288 128 c1468288))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1468416 128 c1468416) (checkChunk_sound 1468544 128 c1468544)) (Checked.append (checkChunk_sound 1468672 128 c1468672) (checkChunk_sound 1468800 128 c1468800))) (Checked.append (Checked.append (checkChunk_sound 1468928 128 c1468928) (checkChunk_sound 1469056 128 c1469056)) (Checked.append (checkChunk_sound 1469184 128 c1469184) (checkChunk_sound 1469312 128 c1469312)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1469440 128 c1469440) (checkChunk_sound 1469568 128 c1469568)) (Checked.append (checkChunk_sound 1469696 128 c1469696) (checkChunk_sound 1469824 128 c1469824))) (Checked.append (Checked.append (checkChunk_sound 1469952 128 c1469952) (checkChunk_sound 1470080 128 c1470080)) (Checked.append (checkChunk_sound 1470208 128 c1470208) (checkChunk_sound 1470336 128 c1470336)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1470464 128 c1470464) (checkChunk_sound 1470592 128 c1470592)) (Checked.append (checkChunk_sound 1470720 128 c1470720) (checkChunk_sound 1470848 128 c1470848))) (Checked.append (Checked.append (checkChunk_sound 1470976 128 c1470976) (checkChunk_sound 1471104 128 c1471104)) (Checked.append (checkChunk_sound 1471232 128 c1471232) (checkChunk_sound 1471360 128 c1471360)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1471488 128 c1471488) (checkChunk_sound 1471616 128 c1471616)) (Checked.append (checkChunk_sound 1471744 128 c1471744) (checkChunk_sound 1471872 128 c1471872))) (Checked.append (Checked.append (checkChunk_sound 1472000 128 c1472000) (checkChunk_sound 1472128 128 c1472128)) (Checked.append (checkChunk_sound 1472256 128 c1472256) (checkChunk_sound 1472384 128 c1472384))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1472512 128 c1472512) (checkChunk_sound 1472640 128 c1472640)) (Checked.append (checkChunk_sound 1472768 128 c1472768) (checkChunk_sound 1472896 128 c1472896))) (Checked.append (Checked.append (checkChunk_sound 1473024 128 c1473024) (checkChunk_sound 1473152 128 c1473152)) (Checked.append (checkChunk_sound 1473280 128 c1473280) (checkChunk_sound 1473408 128 c1473408)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1473536 128 c1473536) (checkChunk_sound 1473664 128 c1473664)) (Checked.append (checkChunk_sound 1473792 128 c1473792) (checkChunk_sound 1473920 128 c1473920))) (Checked.append (Checked.append (checkChunk_sound 1474048 128 c1474048) (checkChunk_sound 1474176 128 c1474176)) (Checked.append (checkChunk_sound 1474304 128 c1474304) (checkChunk_sound 1474432 128 c1474432)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B022
