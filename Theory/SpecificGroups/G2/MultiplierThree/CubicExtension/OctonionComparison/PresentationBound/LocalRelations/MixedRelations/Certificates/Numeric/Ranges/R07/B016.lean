module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1630208, 1638400).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B016
private theorem c1630208 : checkChunk 1630208 128 = true := by decide +kernel
private theorem c1630336 : checkChunk 1630336 128 = true := by decide +kernel
private theorem c1630464 : checkChunk 1630464 128 = true := by decide +kernel
private theorem c1630592 : checkChunk 1630592 128 = true := by decide +kernel
private theorem c1630720 : checkChunk 1630720 128 = true := by decide +kernel
private theorem c1630848 : checkChunk 1630848 128 = true := by decide +kernel
private theorem c1630976 : checkChunk 1630976 128 = true := by decide +kernel
private theorem c1631104 : checkChunk 1631104 128 = true := by decide +kernel
private theorem c1631232 : checkChunk 1631232 128 = true := by decide +kernel
private theorem c1631360 : checkChunk 1631360 128 = true := by decide +kernel
private theorem c1631488 : checkChunk 1631488 128 = true := by decide +kernel
private theorem c1631616 : checkChunk 1631616 128 = true := by decide +kernel
private theorem c1631744 : checkChunk 1631744 128 = true := by decide +kernel
private theorem c1631872 : checkChunk 1631872 128 = true := by decide +kernel
private theorem c1632000 : checkChunk 1632000 128 = true := by decide +kernel
private theorem c1632128 : checkChunk 1632128 128 = true := by decide +kernel
private theorem c1632256 : checkChunk 1632256 128 = true := by decide +kernel
private theorem c1632384 : checkChunk 1632384 128 = true := by decide +kernel
private theorem c1632512 : checkChunk 1632512 128 = true := by decide +kernel
private theorem c1632640 : checkChunk 1632640 128 = true := by decide +kernel
private theorem c1632768 : checkChunk 1632768 128 = true := by decide +kernel
private theorem c1632896 : checkChunk 1632896 128 = true := by decide +kernel
private theorem c1633024 : checkChunk 1633024 128 = true := by decide +kernel
private theorem c1633152 : checkChunk 1633152 128 = true := by decide +kernel
private theorem c1633280 : checkChunk 1633280 128 = true := by decide +kernel
private theorem c1633408 : checkChunk 1633408 128 = true := by decide +kernel
private theorem c1633536 : checkChunk 1633536 128 = true := by decide +kernel
private theorem c1633664 : checkChunk 1633664 128 = true := by decide +kernel
private theorem c1633792 : checkChunk 1633792 128 = true := by decide +kernel
private theorem c1633920 : checkChunk 1633920 128 = true := by decide +kernel
private theorem c1634048 : checkChunk 1634048 128 = true := by decide +kernel
private theorem c1634176 : checkChunk 1634176 128 = true := by decide +kernel
private theorem c1634304 : checkChunk 1634304 128 = true := by decide +kernel
private theorem c1634432 : checkChunk 1634432 128 = true := by decide +kernel
private theorem c1634560 : checkChunk 1634560 128 = true := by decide +kernel
private theorem c1634688 : checkChunk 1634688 128 = true := by decide +kernel
private theorem c1634816 : checkChunk 1634816 128 = true := by decide +kernel
private theorem c1634944 : checkChunk 1634944 128 = true := by decide +kernel
private theorem c1635072 : checkChunk 1635072 128 = true := by decide +kernel
private theorem c1635200 : checkChunk 1635200 128 = true := by decide +kernel
private theorem c1635328 : checkChunk 1635328 128 = true := by decide +kernel
private theorem c1635456 : checkChunk 1635456 128 = true := by decide +kernel
private theorem c1635584 : checkChunk 1635584 128 = true := by decide +kernel
private theorem c1635712 : checkChunk 1635712 128 = true := by decide +kernel
private theorem c1635840 : checkChunk 1635840 128 = true := by decide +kernel
private theorem c1635968 : checkChunk 1635968 128 = true := by decide +kernel
private theorem c1636096 : checkChunk 1636096 128 = true := by decide +kernel
private theorem c1636224 : checkChunk 1636224 128 = true := by decide +kernel
private theorem c1636352 : checkChunk 1636352 128 = true := by decide +kernel
private theorem c1636480 : checkChunk 1636480 128 = true := by decide +kernel
private theorem c1636608 : checkChunk 1636608 128 = true := by decide +kernel
private theorem c1636736 : checkChunk 1636736 128 = true := by decide +kernel
private theorem c1636864 : checkChunk 1636864 128 = true := by decide +kernel
private theorem c1636992 : checkChunk 1636992 128 = true := by decide +kernel
private theorem c1637120 : checkChunk 1637120 128 = true := by decide +kernel
private theorem c1637248 : checkChunk 1637248 128 = true := by decide +kernel
private theorem c1637376 : checkChunk 1637376 128 = true := by decide +kernel
private theorem c1637504 : checkChunk 1637504 128 = true := by decide +kernel
private theorem c1637632 : checkChunk 1637632 128 = true := by decide +kernel
private theorem c1637760 : checkChunk 1637760 128 = true := by decide +kernel
private theorem c1637888 : checkChunk 1637888 128 = true := by decide +kernel
private theorem c1638016 : checkChunk 1638016 128 = true := by decide +kernel
private theorem c1638144 : checkChunk 1638144 128 = true := by decide +kernel
private theorem c1638272 : checkChunk 1638272 128 = true := by decide +kernel

public theorem checked : Checked 1630208 1638400 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1630208 128 c1630208) (checkChunk_sound 1630336 128 c1630336)) (Checked.append (checkChunk_sound 1630464 128 c1630464) (checkChunk_sound 1630592 128 c1630592))) (Checked.append (Checked.append (checkChunk_sound 1630720 128 c1630720) (checkChunk_sound 1630848 128 c1630848)) (Checked.append (checkChunk_sound 1630976 128 c1630976) (checkChunk_sound 1631104 128 c1631104)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1631232 128 c1631232) (checkChunk_sound 1631360 128 c1631360)) (Checked.append (checkChunk_sound 1631488 128 c1631488) (checkChunk_sound 1631616 128 c1631616))) (Checked.append (Checked.append (checkChunk_sound 1631744 128 c1631744) (checkChunk_sound 1631872 128 c1631872)) (Checked.append (checkChunk_sound 1632000 128 c1632000) (checkChunk_sound 1632128 128 c1632128))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1632256 128 c1632256) (checkChunk_sound 1632384 128 c1632384)) (Checked.append (checkChunk_sound 1632512 128 c1632512) (checkChunk_sound 1632640 128 c1632640))) (Checked.append (Checked.append (checkChunk_sound 1632768 128 c1632768) (checkChunk_sound 1632896 128 c1632896)) (Checked.append (checkChunk_sound 1633024 128 c1633024) (checkChunk_sound 1633152 128 c1633152)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1633280 128 c1633280) (checkChunk_sound 1633408 128 c1633408)) (Checked.append (checkChunk_sound 1633536 128 c1633536) (checkChunk_sound 1633664 128 c1633664))) (Checked.append (Checked.append (checkChunk_sound 1633792 128 c1633792) (checkChunk_sound 1633920 128 c1633920)) (Checked.append (checkChunk_sound 1634048 128 c1634048) (checkChunk_sound 1634176 128 c1634176)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1634304 128 c1634304) (checkChunk_sound 1634432 128 c1634432)) (Checked.append (checkChunk_sound 1634560 128 c1634560) (checkChunk_sound 1634688 128 c1634688))) (Checked.append (Checked.append (checkChunk_sound 1634816 128 c1634816) (checkChunk_sound 1634944 128 c1634944)) (Checked.append (checkChunk_sound 1635072 128 c1635072) (checkChunk_sound 1635200 128 c1635200)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1635328 128 c1635328) (checkChunk_sound 1635456 128 c1635456)) (Checked.append (checkChunk_sound 1635584 128 c1635584) (checkChunk_sound 1635712 128 c1635712))) (Checked.append (Checked.append (checkChunk_sound 1635840 128 c1635840) (checkChunk_sound 1635968 128 c1635968)) (Checked.append (checkChunk_sound 1636096 128 c1636096) (checkChunk_sound 1636224 128 c1636224))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1636352 128 c1636352) (checkChunk_sound 1636480 128 c1636480)) (Checked.append (checkChunk_sound 1636608 128 c1636608) (checkChunk_sound 1636736 128 c1636736))) (Checked.append (Checked.append (checkChunk_sound 1636864 128 c1636864) (checkChunk_sound 1636992 128 c1636992)) (Checked.append (checkChunk_sound 1637120 128 c1637120) (checkChunk_sound 1637248 128 c1637248)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1637376 128 c1637376) (checkChunk_sound 1637504 128 c1637504)) (Checked.append (checkChunk_sound 1637632 128 c1637632) (checkChunk_sound 1637760 128 c1637760))) (Checked.append (Checked.append (checkChunk_sound 1637888 128 c1637888) (checkChunk_sound 1638016 128 c1638016)) (Checked.append (checkChunk_sound 1638144 128 c1638144) (checkChunk_sound 1638272 128 c1638272)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B016
