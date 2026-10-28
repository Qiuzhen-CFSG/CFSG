module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1523712, 1531904).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B003
private theorem c1523712 : checkChunk 1523712 128 = true := by decide +kernel
private theorem c1523840 : checkChunk 1523840 128 = true := by decide +kernel
private theorem c1523968 : checkChunk 1523968 128 = true := by decide +kernel
private theorem c1524096 : checkChunk 1524096 128 = true := by decide +kernel
private theorem c1524224 : checkChunk 1524224 128 = true := by decide +kernel
private theorem c1524352 : checkChunk 1524352 128 = true := by decide +kernel
private theorem c1524480 : checkChunk 1524480 128 = true := by decide +kernel
private theorem c1524608 : checkChunk 1524608 128 = true := by decide +kernel
private theorem c1524736 : checkChunk 1524736 128 = true := by decide +kernel
private theorem c1524864 : checkChunk 1524864 128 = true := by decide +kernel
private theorem c1524992 : checkChunk 1524992 128 = true := by decide +kernel
private theorem c1525120 : checkChunk 1525120 128 = true := by decide +kernel
private theorem c1525248 : checkChunk 1525248 128 = true := by decide +kernel
private theorem c1525376 : checkChunk 1525376 128 = true := by decide +kernel
private theorem c1525504 : checkChunk 1525504 128 = true := by decide +kernel
private theorem c1525632 : checkChunk 1525632 128 = true := by decide +kernel
private theorem c1525760 : checkChunk 1525760 128 = true := by decide +kernel
private theorem c1525888 : checkChunk 1525888 128 = true := by decide +kernel
private theorem c1526016 : checkChunk 1526016 128 = true := by decide +kernel
private theorem c1526144 : checkChunk 1526144 128 = true := by decide +kernel
private theorem c1526272 : checkChunk 1526272 128 = true := by decide +kernel
private theorem c1526400 : checkChunk 1526400 128 = true := by decide +kernel
private theorem c1526528 : checkChunk 1526528 128 = true := by decide +kernel
private theorem c1526656 : checkChunk 1526656 128 = true := by decide +kernel
private theorem c1526784 : checkChunk 1526784 128 = true := by decide +kernel
private theorem c1526912 : checkChunk 1526912 128 = true := by decide +kernel
private theorem c1527040 : checkChunk 1527040 128 = true := by decide +kernel
private theorem c1527168 : checkChunk 1527168 128 = true := by decide +kernel
private theorem c1527296 : checkChunk 1527296 128 = true := by decide +kernel
private theorem c1527424 : checkChunk 1527424 128 = true := by decide +kernel
private theorem c1527552 : checkChunk 1527552 128 = true := by decide +kernel
private theorem c1527680 : checkChunk 1527680 128 = true := by decide +kernel
private theorem c1527808 : checkChunk 1527808 128 = true := by decide +kernel
private theorem c1527936 : checkChunk 1527936 128 = true := by decide +kernel
private theorem c1528064 : checkChunk 1528064 128 = true := by decide +kernel
private theorem c1528192 : checkChunk 1528192 128 = true := by decide +kernel
private theorem c1528320 : checkChunk 1528320 128 = true := by decide +kernel
private theorem c1528448 : checkChunk 1528448 128 = true := by decide +kernel
private theorem c1528576 : checkChunk 1528576 128 = true := by decide +kernel
private theorem c1528704 : checkChunk 1528704 128 = true := by decide +kernel
private theorem c1528832 : checkChunk 1528832 128 = true := by decide +kernel
private theorem c1528960 : checkChunk 1528960 128 = true := by decide +kernel
private theorem c1529088 : checkChunk 1529088 128 = true := by decide +kernel
private theorem c1529216 : checkChunk 1529216 128 = true := by decide +kernel
private theorem c1529344 : checkChunk 1529344 128 = true := by decide +kernel
private theorem c1529472 : checkChunk 1529472 128 = true := by decide +kernel
private theorem c1529600 : checkChunk 1529600 128 = true := by decide +kernel
private theorem c1529728 : checkChunk 1529728 128 = true := by decide +kernel
private theorem c1529856 : checkChunk 1529856 128 = true := by decide +kernel
private theorem c1529984 : checkChunk 1529984 128 = true := by decide +kernel
private theorem c1530112 : checkChunk 1530112 128 = true := by decide +kernel
private theorem c1530240 : checkChunk 1530240 128 = true := by decide +kernel
private theorem c1530368 : checkChunk 1530368 128 = true := by decide +kernel
private theorem c1530496 : checkChunk 1530496 128 = true := by decide +kernel
private theorem c1530624 : checkChunk 1530624 128 = true := by decide +kernel
private theorem c1530752 : checkChunk 1530752 128 = true := by decide +kernel
private theorem c1530880 : checkChunk 1530880 128 = true := by decide +kernel
private theorem c1531008 : checkChunk 1531008 128 = true := by decide +kernel
private theorem c1531136 : checkChunk 1531136 128 = true := by decide +kernel
private theorem c1531264 : checkChunk 1531264 128 = true := by decide +kernel
private theorem c1531392 : checkChunk 1531392 128 = true := by decide +kernel
private theorem c1531520 : checkChunk 1531520 128 = true := by decide +kernel
private theorem c1531648 : checkChunk 1531648 128 = true := by decide +kernel
private theorem c1531776 : checkChunk 1531776 128 = true := by decide +kernel

public theorem checked : Checked 1523712 1531904 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1523712 128 c1523712) (checkChunk_sound 1523840 128 c1523840)) (Checked.append (checkChunk_sound 1523968 128 c1523968) (checkChunk_sound 1524096 128 c1524096))) (Checked.append (Checked.append (checkChunk_sound 1524224 128 c1524224) (checkChunk_sound 1524352 128 c1524352)) (Checked.append (checkChunk_sound 1524480 128 c1524480) (checkChunk_sound 1524608 128 c1524608)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1524736 128 c1524736) (checkChunk_sound 1524864 128 c1524864)) (Checked.append (checkChunk_sound 1524992 128 c1524992) (checkChunk_sound 1525120 128 c1525120))) (Checked.append (Checked.append (checkChunk_sound 1525248 128 c1525248) (checkChunk_sound 1525376 128 c1525376)) (Checked.append (checkChunk_sound 1525504 128 c1525504) (checkChunk_sound 1525632 128 c1525632))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1525760 128 c1525760) (checkChunk_sound 1525888 128 c1525888)) (Checked.append (checkChunk_sound 1526016 128 c1526016) (checkChunk_sound 1526144 128 c1526144))) (Checked.append (Checked.append (checkChunk_sound 1526272 128 c1526272) (checkChunk_sound 1526400 128 c1526400)) (Checked.append (checkChunk_sound 1526528 128 c1526528) (checkChunk_sound 1526656 128 c1526656)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1526784 128 c1526784) (checkChunk_sound 1526912 128 c1526912)) (Checked.append (checkChunk_sound 1527040 128 c1527040) (checkChunk_sound 1527168 128 c1527168))) (Checked.append (Checked.append (checkChunk_sound 1527296 128 c1527296) (checkChunk_sound 1527424 128 c1527424)) (Checked.append (checkChunk_sound 1527552 128 c1527552) (checkChunk_sound 1527680 128 c1527680)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1527808 128 c1527808) (checkChunk_sound 1527936 128 c1527936)) (Checked.append (checkChunk_sound 1528064 128 c1528064) (checkChunk_sound 1528192 128 c1528192))) (Checked.append (Checked.append (checkChunk_sound 1528320 128 c1528320) (checkChunk_sound 1528448 128 c1528448)) (Checked.append (checkChunk_sound 1528576 128 c1528576) (checkChunk_sound 1528704 128 c1528704)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1528832 128 c1528832) (checkChunk_sound 1528960 128 c1528960)) (Checked.append (checkChunk_sound 1529088 128 c1529088) (checkChunk_sound 1529216 128 c1529216))) (Checked.append (Checked.append (checkChunk_sound 1529344 128 c1529344) (checkChunk_sound 1529472 128 c1529472)) (Checked.append (checkChunk_sound 1529600 128 c1529600) (checkChunk_sound 1529728 128 c1529728))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1529856 128 c1529856) (checkChunk_sound 1529984 128 c1529984)) (Checked.append (checkChunk_sound 1530112 128 c1530112) (checkChunk_sound 1530240 128 c1530240))) (Checked.append (Checked.append (checkChunk_sound 1530368 128 c1530368) (checkChunk_sound 1530496 128 c1530496)) (Checked.append (checkChunk_sound 1530624 128 c1530624) (checkChunk_sound 1530752 128 c1530752)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1530880 128 c1530880) (checkChunk_sound 1531008 128 c1531008)) (Checked.append (checkChunk_sound 1531136 128 c1531136) (checkChunk_sound 1531264 128 c1531264))) (Checked.append (Checked.append (checkChunk_sound 1531392 128 c1531392) (checkChunk_sound 1531520 128 c1531520)) (Checked.append (checkChunk_sound 1531648 128 c1531648) (checkChunk_sound 1531776 128 c1531776)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B003
