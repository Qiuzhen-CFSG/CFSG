module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1646592, 1654784).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B018
private theorem c1646592 : checkChunk 1646592 128 = true := by decide +kernel
private theorem c1646720 : checkChunk 1646720 128 = true := by decide +kernel
private theorem c1646848 : checkChunk 1646848 128 = true := by decide +kernel
private theorem c1646976 : checkChunk 1646976 128 = true := by decide +kernel
private theorem c1647104 : checkChunk 1647104 128 = true := by decide +kernel
private theorem c1647232 : checkChunk 1647232 128 = true := by decide +kernel
private theorem c1647360 : checkChunk 1647360 128 = true := by decide +kernel
private theorem c1647488 : checkChunk 1647488 128 = true := by decide +kernel
private theorem c1647616 : checkChunk 1647616 128 = true := by decide +kernel
private theorem c1647744 : checkChunk 1647744 128 = true := by decide +kernel
private theorem c1647872 : checkChunk 1647872 128 = true := by decide +kernel
private theorem c1648000 : checkChunk 1648000 128 = true := by decide +kernel
private theorem c1648128 : checkChunk 1648128 128 = true := by decide +kernel
private theorem c1648256 : checkChunk 1648256 128 = true := by decide +kernel
private theorem c1648384 : checkChunk 1648384 128 = true := by decide +kernel
private theorem c1648512 : checkChunk 1648512 128 = true := by decide +kernel
private theorem c1648640 : checkChunk 1648640 128 = true := by decide +kernel
private theorem c1648768 : checkChunk 1648768 128 = true := by decide +kernel
private theorem c1648896 : checkChunk 1648896 128 = true := by decide +kernel
private theorem c1649024 : checkChunk 1649024 128 = true := by decide +kernel
private theorem c1649152 : checkChunk 1649152 128 = true := by decide +kernel
private theorem c1649280 : checkChunk 1649280 128 = true := by decide +kernel
private theorem c1649408 : checkChunk 1649408 128 = true := by decide +kernel
private theorem c1649536 : checkChunk 1649536 128 = true := by decide +kernel
private theorem c1649664 : checkChunk 1649664 128 = true := by decide +kernel
private theorem c1649792 : checkChunk 1649792 128 = true := by decide +kernel
private theorem c1649920 : checkChunk 1649920 128 = true := by decide +kernel
private theorem c1650048 : checkChunk 1650048 128 = true := by decide +kernel
private theorem c1650176 : checkChunk 1650176 128 = true := by decide +kernel
private theorem c1650304 : checkChunk 1650304 128 = true := by decide +kernel
private theorem c1650432 : checkChunk 1650432 128 = true := by decide +kernel
private theorem c1650560 : checkChunk 1650560 128 = true := by decide +kernel
private theorem c1650688 : checkChunk 1650688 128 = true := by decide +kernel
private theorem c1650816 : checkChunk 1650816 128 = true := by decide +kernel
private theorem c1650944 : checkChunk 1650944 128 = true := by decide +kernel
private theorem c1651072 : checkChunk 1651072 128 = true := by decide +kernel
private theorem c1651200 : checkChunk 1651200 128 = true := by decide +kernel
private theorem c1651328 : checkChunk 1651328 128 = true := by decide +kernel
private theorem c1651456 : checkChunk 1651456 128 = true := by decide +kernel
private theorem c1651584 : checkChunk 1651584 128 = true := by decide +kernel
private theorem c1651712 : checkChunk 1651712 128 = true := by decide +kernel
private theorem c1651840 : checkChunk 1651840 128 = true := by decide +kernel
private theorem c1651968 : checkChunk 1651968 128 = true := by decide +kernel
private theorem c1652096 : checkChunk 1652096 128 = true := by decide +kernel
private theorem c1652224 : checkChunk 1652224 128 = true := by decide +kernel
private theorem c1652352 : checkChunk 1652352 128 = true := by decide +kernel
private theorem c1652480 : checkChunk 1652480 128 = true := by decide +kernel
private theorem c1652608 : checkChunk 1652608 128 = true := by decide +kernel
private theorem c1652736 : checkChunk 1652736 128 = true := by decide +kernel
private theorem c1652864 : checkChunk 1652864 128 = true := by decide +kernel
private theorem c1652992 : checkChunk 1652992 128 = true := by decide +kernel
private theorem c1653120 : checkChunk 1653120 128 = true := by decide +kernel
private theorem c1653248 : checkChunk 1653248 128 = true := by decide +kernel
private theorem c1653376 : checkChunk 1653376 128 = true := by decide +kernel
private theorem c1653504 : checkChunk 1653504 128 = true := by decide +kernel
private theorem c1653632 : checkChunk 1653632 128 = true := by decide +kernel
private theorem c1653760 : checkChunk 1653760 128 = true := by decide +kernel
private theorem c1653888 : checkChunk 1653888 128 = true := by decide +kernel
private theorem c1654016 : checkChunk 1654016 128 = true := by decide +kernel
private theorem c1654144 : checkChunk 1654144 128 = true := by decide +kernel
private theorem c1654272 : checkChunk 1654272 128 = true := by decide +kernel
private theorem c1654400 : checkChunk 1654400 128 = true := by decide +kernel
private theorem c1654528 : checkChunk 1654528 128 = true := by decide +kernel
private theorem c1654656 : checkChunk 1654656 128 = true := by decide +kernel

public theorem checked : Checked 1646592 1654784 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1646592 128 c1646592) (checkChunk_sound 1646720 128 c1646720)) (Checked.append (checkChunk_sound 1646848 128 c1646848) (checkChunk_sound 1646976 128 c1646976))) (Checked.append (Checked.append (checkChunk_sound 1647104 128 c1647104) (checkChunk_sound 1647232 128 c1647232)) (Checked.append (checkChunk_sound 1647360 128 c1647360) (checkChunk_sound 1647488 128 c1647488)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1647616 128 c1647616) (checkChunk_sound 1647744 128 c1647744)) (Checked.append (checkChunk_sound 1647872 128 c1647872) (checkChunk_sound 1648000 128 c1648000))) (Checked.append (Checked.append (checkChunk_sound 1648128 128 c1648128) (checkChunk_sound 1648256 128 c1648256)) (Checked.append (checkChunk_sound 1648384 128 c1648384) (checkChunk_sound 1648512 128 c1648512))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1648640 128 c1648640) (checkChunk_sound 1648768 128 c1648768)) (Checked.append (checkChunk_sound 1648896 128 c1648896) (checkChunk_sound 1649024 128 c1649024))) (Checked.append (Checked.append (checkChunk_sound 1649152 128 c1649152) (checkChunk_sound 1649280 128 c1649280)) (Checked.append (checkChunk_sound 1649408 128 c1649408) (checkChunk_sound 1649536 128 c1649536)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1649664 128 c1649664) (checkChunk_sound 1649792 128 c1649792)) (Checked.append (checkChunk_sound 1649920 128 c1649920) (checkChunk_sound 1650048 128 c1650048))) (Checked.append (Checked.append (checkChunk_sound 1650176 128 c1650176) (checkChunk_sound 1650304 128 c1650304)) (Checked.append (checkChunk_sound 1650432 128 c1650432) (checkChunk_sound 1650560 128 c1650560)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1650688 128 c1650688) (checkChunk_sound 1650816 128 c1650816)) (Checked.append (checkChunk_sound 1650944 128 c1650944) (checkChunk_sound 1651072 128 c1651072))) (Checked.append (Checked.append (checkChunk_sound 1651200 128 c1651200) (checkChunk_sound 1651328 128 c1651328)) (Checked.append (checkChunk_sound 1651456 128 c1651456) (checkChunk_sound 1651584 128 c1651584)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1651712 128 c1651712) (checkChunk_sound 1651840 128 c1651840)) (Checked.append (checkChunk_sound 1651968 128 c1651968) (checkChunk_sound 1652096 128 c1652096))) (Checked.append (Checked.append (checkChunk_sound 1652224 128 c1652224) (checkChunk_sound 1652352 128 c1652352)) (Checked.append (checkChunk_sound 1652480 128 c1652480) (checkChunk_sound 1652608 128 c1652608))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1652736 128 c1652736) (checkChunk_sound 1652864 128 c1652864)) (Checked.append (checkChunk_sound 1652992 128 c1652992) (checkChunk_sound 1653120 128 c1653120))) (Checked.append (Checked.append (checkChunk_sound 1653248 128 c1653248) (checkChunk_sound 1653376 128 c1653376)) (Checked.append (checkChunk_sound 1653504 128 c1653504) (checkChunk_sound 1653632 128 c1653632)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1653760 128 c1653760) (checkChunk_sound 1653888 128 c1653888)) (Checked.append (checkChunk_sound 1654016 128 c1654016) (checkChunk_sound 1654144 128 c1654144))) (Checked.append (Checked.append (checkChunk_sound 1654272 128 c1654272) (checkChunk_sound 1654400 128 c1654400)) (Checked.append (checkChunk_sound 1654528 128 c1654528) (checkChunk_sound 1654656 128 c1654656)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B018
