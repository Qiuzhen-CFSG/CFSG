module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1679360, 1687552).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B022
private theorem c1679360 : checkChunk 1679360 128 = true := by decide +kernel
private theorem c1679488 : checkChunk 1679488 128 = true := by decide +kernel
private theorem c1679616 : checkChunk 1679616 128 = true := by decide +kernel
private theorem c1679744 : checkChunk 1679744 128 = true := by decide +kernel
private theorem c1679872 : checkChunk 1679872 128 = true := by decide +kernel
private theorem c1680000 : checkChunk 1680000 128 = true := by decide +kernel
private theorem c1680128 : checkChunk 1680128 128 = true := by decide +kernel
private theorem c1680256 : checkChunk 1680256 128 = true := by decide +kernel
private theorem c1680384 : checkChunk 1680384 128 = true := by decide +kernel
private theorem c1680512 : checkChunk 1680512 128 = true := by decide +kernel
private theorem c1680640 : checkChunk 1680640 128 = true := by decide +kernel
private theorem c1680768 : checkChunk 1680768 128 = true := by decide +kernel
private theorem c1680896 : checkChunk 1680896 128 = true := by decide +kernel
private theorem c1681024 : checkChunk 1681024 128 = true := by decide +kernel
private theorem c1681152 : checkChunk 1681152 128 = true := by decide +kernel
private theorem c1681280 : checkChunk 1681280 128 = true := by decide +kernel
private theorem c1681408 : checkChunk 1681408 128 = true := by decide +kernel
private theorem c1681536 : checkChunk 1681536 128 = true := by decide +kernel
private theorem c1681664 : checkChunk 1681664 128 = true := by decide +kernel
private theorem c1681792 : checkChunk 1681792 128 = true := by decide +kernel
private theorem c1681920 : checkChunk 1681920 128 = true := by decide +kernel
private theorem c1682048 : checkChunk 1682048 128 = true := by decide +kernel
private theorem c1682176 : checkChunk 1682176 128 = true := by decide +kernel
private theorem c1682304 : checkChunk 1682304 128 = true := by decide +kernel
private theorem c1682432 : checkChunk 1682432 128 = true := by decide +kernel
private theorem c1682560 : checkChunk 1682560 128 = true := by decide +kernel
private theorem c1682688 : checkChunk 1682688 128 = true := by decide +kernel
private theorem c1682816 : checkChunk 1682816 128 = true := by decide +kernel
private theorem c1682944 : checkChunk 1682944 128 = true := by decide +kernel
private theorem c1683072 : checkChunk 1683072 128 = true := by decide +kernel
private theorem c1683200 : checkChunk 1683200 128 = true := by decide +kernel
private theorem c1683328 : checkChunk 1683328 128 = true := by decide +kernel
private theorem c1683456 : checkChunk 1683456 128 = true := by decide +kernel
private theorem c1683584 : checkChunk 1683584 128 = true := by decide +kernel
private theorem c1683712 : checkChunk 1683712 128 = true := by decide +kernel
private theorem c1683840 : checkChunk 1683840 128 = true := by decide +kernel
private theorem c1683968 : checkChunk 1683968 128 = true := by decide +kernel
private theorem c1684096 : checkChunk 1684096 128 = true := by decide +kernel
private theorem c1684224 : checkChunk 1684224 128 = true := by decide +kernel
private theorem c1684352 : checkChunk 1684352 128 = true := by decide +kernel
private theorem c1684480 : checkChunk 1684480 128 = true := by decide +kernel
private theorem c1684608 : checkChunk 1684608 128 = true := by decide +kernel
private theorem c1684736 : checkChunk 1684736 128 = true := by decide +kernel
private theorem c1684864 : checkChunk 1684864 128 = true := by decide +kernel
private theorem c1684992 : checkChunk 1684992 128 = true := by decide +kernel
private theorem c1685120 : checkChunk 1685120 128 = true := by decide +kernel
private theorem c1685248 : checkChunk 1685248 128 = true := by decide +kernel
private theorem c1685376 : checkChunk 1685376 128 = true := by decide +kernel
private theorem c1685504 : checkChunk 1685504 128 = true := by decide +kernel
private theorem c1685632 : checkChunk 1685632 128 = true := by decide +kernel
private theorem c1685760 : checkChunk 1685760 128 = true := by decide +kernel
private theorem c1685888 : checkChunk 1685888 128 = true := by decide +kernel
private theorem c1686016 : checkChunk 1686016 128 = true := by decide +kernel
private theorem c1686144 : checkChunk 1686144 128 = true := by decide +kernel
private theorem c1686272 : checkChunk 1686272 128 = true := by decide +kernel
private theorem c1686400 : checkChunk 1686400 128 = true := by decide +kernel
private theorem c1686528 : checkChunk 1686528 128 = true := by decide +kernel
private theorem c1686656 : checkChunk 1686656 128 = true := by decide +kernel
private theorem c1686784 : checkChunk 1686784 128 = true := by decide +kernel
private theorem c1686912 : checkChunk 1686912 128 = true := by decide +kernel
private theorem c1687040 : checkChunk 1687040 128 = true := by decide +kernel
private theorem c1687168 : checkChunk 1687168 128 = true := by decide +kernel
private theorem c1687296 : checkChunk 1687296 128 = true := by decide +kernel
private theorem c1687424 : checkChunk 1687424 128 = true := by decide +kernel

public theorem checked : Checked 1679360 1687552 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1679360 128 c1679360) (checkChunk_sound 1679488 128 c1679488)) (Checked.append (checkChunk_sound 1679616 128 c1679616) (checkChunk_sound 1679744 128 c1679744))) (Checked.append (Checked.append (checkChunk_sound 1679872 128 c1679872) (checkChunk_sound 1680000 128 c1680000)) (Checked.append (checkChunk_sound 1680128 128 c1680128) (checkChunk_sound 1680256 128 c1680256)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1680384 128 c1680384) (checkChunk_sound 1680512 128 c1680512)) (Checked.append (checkChunk_sound 1680640 128 c1680640) (checkChunk_sound 1680768 128 c1680768))) (Checked.append (Checked.append (checkChunk_sound 1680896 128 c1680896) (checkChunk_sound 1681024 128 c1681024)) (Checked.append (checkChunk_sound 1681152 128 c1681152) (checkChunk_sound 1681280 128 c1681280))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1681408 128 c1681408) (checkChunk_sound 1681536 128 c1681536)) (Checked.append (checkChunk_sound 1681664 128 c1681664) (checkChunk_sound 1681792 128 c1681792))) (Checked.append (Checked.append (checkChunk_sound 1681920 128 c1681920) (checkChunk_sound 1682048 128 c1682048)) (Checked.append (checkChunk_sound 1682176 128 c1682176) (checkChunk_sound 1682304 128 c1682304)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1682432 128 c1682432) (checkChunk_sound 1682560 128 c1682560)) (Checked.append (checkChunk_sound 1682688 128 c1682688) (checkChunk_sound 1682816 128 c1682816))) (Checked.append (Checked.append (checkChunk_sound 1682944 128 c1682944) (checkChunk_sound 1683072 128 c1683072)) (Checked.append (checkChunk_sound 1683200 128 c1683200) (checkChunk_sound 1683328 128 c1683328)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1683456 128 c1683456) (checkChunk_sound 1683584 128 c1683584)) (Checked.append (checkChunk_sound 1683712 128 c1683712) (checkChunk_sound 1683840 128 c1683840))) (Checked.append (Checked.append (checkChunk_sound 1683968 128 c1683968) (checkChunk_sound 1684096 128 c1684096)) (Checked.append (checkChunk_sound 1684224 128 c1684224) (checkChunk_sound 1684352 128 c1684352)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1684480 128 c1684480) (checkChunk_sound 1684608 128 c1684608)) (Checked.append (checkChunk_sound 1684736 128 c1684736) (checkChunk_sound 1684864 128 c1684864))) (Checked.append (Checked.append (checkChunk_sound 1684992 128 c1684992) (checkChunk_sound 1685120 128 c1685120)) (Checked.append (checkChunk_sound 1685248 128 c1685248) (checkChunk_sound 1685376 128 c1685376))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1685504 128 c1685504) (checkChunk_sound 1685632 128 c1685632)) (Checked.append (checkChunk_sound 1685760 128 c1685760) (checkChunk_sound 1685888 128 c1685888))) (Checked.append (Checked.append (checkChunk_sound 1686016 128 c1686016) (checkChunk_sound 1686144 128 c1686144)) (Checked.append (checkChunk_sound 1686272 128 c1686272) (checkChunk_sound 1686400 128 c1686400)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1686528 128 c1686528) (checkChunk_sound 1686656 128 c1686656)) (Checked.append (checkChunk_sound 1686784 128 c1686784) (checkChunk_sound 1686912 128 c1686912))) (Checked.append (Checked.append (checkChunk_sound 1687040 128 c1687040) (checkChunk_sound 1687168 128 c1687168)) (Checked.append (checkChunk_sound 1687296 128 c1687296) (checkChunk_sound 1687424 128 c1687424)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B022
