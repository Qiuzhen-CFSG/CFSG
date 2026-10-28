module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1556480, 1564672).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B007
private theorem c1556480 : checkChunk 1556480 128 = true := by decide +kernel
private theorem c1556608 : checkChunk 1556608 128 = true := by decide +kernel
private theorem c1556736 : checkChunk 1556736 128 = true := by decide +kernel
private theorem c1556864 : checkChunk 1556864 128 = true := by decide +kernel
private theorem c1556992 : checkChunk 1556992 128 = true := by decide +kernel
private theorem c1557120 : checkChunk 1557120 128 = true := by decide +kernel
private theorem c1557248 : checkChunk 1557248 128 = true := by decide +kernel
private theorem c1557376 : checkChunk 1557376 128 = true := by decide +kernel
private theorem c1557504 : checkChunk 1557504 128 = true := by decide +kernel
private theorem c1557632 : checkChunk 1557632 128 = true := by decide +kernel
private theorem c1557760 : checkChunk 1557760 128 = true := by decide +kernel
private theorem c1557888 : checkChunk 1557888 128 = true := by decide +kernel
private theorem c1558016 : checkChunk 1558016 128 = true := by decide +kernel
private theorem c1558144 : checkChunk 1558144 128 = true := by decide +kernel
private theorem c1558272 : checkChunk 1558272 128 = true := by decide +kernel
private theorem c1558400 : checkChunk 1558400 128 = true := by decide +kernel
private theorem c1558528 : checkChunk 1558528 128 = true := by decide +kernel
private theorem c1558656 : checkChunk 1558656 128 = true := by decide +kernel
private theorem c1558784 : checkChunk 1558784 128 = true := by decide +kernel
private theorem c1558912 : checkChunk 1558912 128 = true := by decide +kernel
private theorem c1559040 : checkChunk 1559040 128 = true := by decide +kernel
private theorem c1559168 : checkChunk 1559168 128 = true := by decide +kernel
private theorem c1559296 : checkChunk 1559296 128 = true := by decide +kernel
private theorem c1559424 : checkChunk 1559424 128 = true := by decide +kernel
private theorem c1559552 : checkChunk 1559552 128 = true := by decide +kernel
private theorem c1559680 : checkChunk 1559680 128 = true := by decide +kernel
private theorem c1559808 : checkChunk 1559808 128 = true := by decide +kernel
private theorem c1559936 : checkChunk 1559936 128 = true := by decide +kernel
private theorem c1560064 : checkChunk 1560064 128 = true := by decide +kernel
private theorem c1560192 : checkChunk 1560192 128 = true := by decide +kernel
private theorem c1560320 : checkChunk 1560320 128 = true := by decide +kernel
private theorem c1560448 : checkChunk 1560448 128 = true := by decide +kernel
private theorem c1560576 : checkChunk 1560576 128 = true := by decide +kernel
private theorem c1560704 : checkChunk 1560704 128 = true := by decide +kernel
private theorem c1560832 : checkChunk 1560832 128 = true := by decide +kernel
private theorem c1560960 : checkChunk 1560960 128 = true := by decide +kernel
private theorem c1561088 : checkChunk 1561088 128 = true := by decide +kernel
private theorem c1561216 : checkChunk 1561216 128 = true := by decide +kernel
private theorem c1561344 : checkChunk 1561344 128 = true := by decide +kernel
private theorem c1561472 : checkChunk 1561472 128 = true := by decide +kernel
private theorem c1561600 : checkChunk 1561600 128 = true := by decide +kernel
private theorem c1561728 : checkChunk 1561728 128 = true := by decide +kernel
private theorem c1561856 : checkChunk 1561856 128 = true := by decide +kernel
private theorem c1561984 : checkChunk 1561984 128 = true := by decide +kernel
private theorem c1562112 : checkChunk 1562112 128 = true := by decide +kernel
private theorem c1562240 : checkChunk 1562240 128 = true := by decide +kernel
private theorem c1562368 : checkChunk 1562368 128 = true := by decide +kernel
private theorem c1562496 : checkChunk 1562496 128 = true := by decide +kernel
private theorem c1562624 : checkChunk 1562624 128 = true := by decide +kernel
private theorem c1562752 : checkChunk 1562752 128 = true := by decide +kernel
private theorem c1562880 : checkChunk 1562880 128 = true := by decide +kernel
private theorem c1563008 : checkChunk 1563008 128 = true := by decide +kernel
private theorem c1563136 : checkChunk 1563136 128 = true := by decide +kernel
private theorem c1563264 : checkChunk 1563264 128 = true := by decide +kernel
private theorem c1563392 : checkChunk 1563392 128 = true := by decide +kernel
private theorem c1563520 : checkChunk 1563520 128 = true := by decide +kernel
private theorem c1563648 : checkChunk 1563648 128 = true := by decide +kernel
private theorem c1563776 : checkChunk 1563776 128 = true := by decide +kernel
private theorem c1563904 : checkChunk 1563904 128 = true := by decide +kernel
private theorem c1564032 : checkChunk 1564032 128 = true := by decide +kernel
private theorem c1564160 : checkChunk 1564160 128 = true := by decide +kernel
private theorem c1564288 : checkChunk 1564288 128 = true := by decide +kernel
private theorem c1564416 : checkChunk 1564416 128 = true := by decide +kernel
private theorem c1564544 : checkChunk 1564544 128 = true := by decide +kernel

public theorem checked : Checked 1556480 1564672 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1556480 128 c1556480) (checkChunk_sound 1556608 128 c1556608)) (Checked.append (checkChunk_sound 1556736 128 c1556736) (checkChunk_sound 1556864 128 c1556864))) (Checked.append (Checked.append (checkChunk_sound 1556992 128 c1556992) (checkChunk_sound 1557120 128 c1557120)) (Checked.append (checkChunk_sound 1557248 128 c1557248) (checkChunk_sound 1557376 128 c1557376)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1557504 128 c1557504) (checkChunk_sound 1557632 128 c1557632)) (Checked.append (checkChunk_sound 1557760 128 c1557760) (checkChunk_sound 1557888 128 c1557888))) (Checked.append (Checked.append (checkChunk_sound 1558016 128 c1558016) (checkChunk_sound 1558144 128 c1558144)) (Checked.append (checkChunk_sound 1558272 128 c1558272) (checkChunk_sound 1558400 128 c1558400))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1558528 128 c1558528) (checkChunk_sound 1558656 128 c1558656)) (Checked.append (checkChunk_sound 1558784 128 c1558784) (checkChunk_sound 1558912 128 c1558912))) (Checked.append (Checked.append (checkChunk_sound 1559040 128 c1559040) (checkChunk_sound 1559168 128 c1559168)) (Checked.append (checkChunk_sound 1559296 128 c1559296) (checkChunk_sound 1559424 128 c1559424)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1559552 128 c1559552) (checkChunk_sound 1559680 128 c1559680)) (Checked.append (checkChunk_sound 1559808 128 c1559808) (checkChunk_sound 1559936 128 c1559936))) (Checked.append (Checked.append (checkChunk_sound 1560064 128 c1560064) (checkChunk_sound 1560192 128 c1560192)) (Checked.append (checkChunk_sound 1560320 128 c1560320) (checkChunk_sound 1560448 128 c1560448)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1560576 128 c1560576) (checkChunk_sound 1560704 128 c1560704)) (Checked.append (checkChunk_sound 1560832 128 c1560832) (checkChunk_sound 1560960 128 c1560960))) (Checked.append (Checked.append (checkChunk_sound 1561088 128 c1561088) (checkChunk_sound 1561216 128 c1561216)) (Checked.append (checkChunk_sound 1561344 128 c1561344) (checkChunk_sound 1561472 128 c1561472)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1561600 128 c1561600) (checkChunk_sound 1561728 128 c1561728)) (Checked.append (checkChunk_sound 1561856 128 c1561856) (checkChunk_sound 1561984 128 c1561984))) (Checked.append (Checked.append (checkChunk_sound 1562112 128 c1562112) (checkChunk_sound 1562240 128 c1562240)) (Checked.append (checkChunk_sound 1562368 128 c1562368) (checkChunk_sound 1562496 128 c1562496))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1562624 128 c1562624) (checkChunk_sound 1562752 128 c1562752)) (Checked.append (checkChunk_sound 1562880 128 c1562880) (checkChunk_sound 1563008 128 c1563008))) (Checked.append (Checked.append (checkChunk_sound 1563136 128 c1563136) (checkChunk_sound 1563264 128 c1563264)) (Checked.append (checkChunk_sound 1563392 128 c1563392) (checkChunk_sound 1563520 128 c1563520)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1563648 128 c1563648) (checkChunk_sound 1563776 128 c1563776)) (Checked.append (checkChunk_sound 1563904 128 c1563904) (checkChunk_sound 1564032 128 c1564032))) (Checked.append (Checked.append (checkChunk_sound 1564160 128 c1564160) (checkChunk_sound 1564288 128 c1564288)) (Checked.append (checkChunk_sound 1564416 128 c1564416) (checkChunk_sound 1564544 128 c1564544)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B007
