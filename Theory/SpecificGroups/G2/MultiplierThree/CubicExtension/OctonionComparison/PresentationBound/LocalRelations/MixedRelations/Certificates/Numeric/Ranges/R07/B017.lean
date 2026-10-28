module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1638400, 1646592).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B017
private theorem c1638400 : checkChunk 1638400 128 = true := by decide +kernel
private theorem c1638528 : checkChunk 1638528 128 = true := by decide +kernel
private theorem c1638656 : checkChunk 1638656 128 = true := by decide +kernel
private theorem c1638784 : checkChunk 1638784 128 = true := by decide +kernel
private theorem c1638912 : checkChunk 1638912 128 = true := by decide +kernel
private theorem c1639040 : checkChunk 1639040 128 = true := by decide +kernel
private theorem c1639168 : checkChunk 1639168 128 = true := by decide +kernel
private theorem c1639296 : checkChunk 1639296 128 = true := by decide +kernel
private theorem c1639424 : checkChunk 1639424 128 = true := by decide +kernel
private theorem c1639552 : checkChunk 1639552 128 = true := by decide +kernel
private theorem c1639680 : checkChunk 1639680 128 = true := by decide +kernel
private theorem c1639808 : checkChunk 1639808 128 = true := by decide +kernel
private theorem c1639936 : checkChunk 1639936 128 = true := by decide +kernel
private theorem c1640064 : checkChunk 1640064 128 = true := by decide +kernel
private theorem c1640192 : checkChunk 1640192 128 = true := by decide +kernel
private theorem c1640320 : checkChunk 1640320 128 = true := by decide +kernel
private theorem c1640448 : checkChunk 1640448 128 = true := by decide +kernel
private theorem c1640576 : checkChunk 1640576 128 = true := by decide +kernel
private theorem c1640704 : checkChunk 1640704 128 = true := by decide +kernel
private theorem c1640832 : checkChunk 1640832 128 = true := by decide +kernel
private theorem c1640960 : checkChunk 1640960 128 = true := by decide +kernel
private theorem c1641088 : checkChunk 1641088 128 = true := by decide +kernel
private theorem c1641216 : checkChunk 1641216 128 = true := by decide +kernel
private theorem c1641344 : checkChunk 1641344 128 = true := by decide +kernel
private theorem c1641472 : checkChunk 1641472 128 = true := by decide +kernel
private theorem c1641600 : checkChunk 1641600 128 = true := by decide +kernel
private theorem c1641728 : checkChunk 1641728 128 = true := by decide +kernel
private theorem c1641856 : checkChunk 1641856 128 = true := by decide +kernel
private theorem c1641984 : checkChunk 1641984 128 = true := by decide +kernel
private theorem c1642112 : checkChunk 1642112 128 = true := by decide +kernel
private theorem c1642240 : checkChunk 1642240 128 = true := by decide +kernel
private theorem c1642368 : checkChunk 1642368 128 = true := by decide +kernel
private theorem c1642496 : checkChunk 1642496 128 = true := by decide +kernel
private theorem c1642624 : checkChunk 1642624 128 = true := by decide +kernel
private theorem c1642752 : checkChunk 1642752 128 = true := by decide +kernel
private theorem c1642880 : checkChunk 1642880 128 = true := by decide +kernel
private theorem c1643008 : checkChunk 1643008 128 = true := by decide +kernel
private theorem c1643136 : checkChunk 1643136 128 = true := by decide +kernel
private theorem c1643264 : checkChunk 1643264 128 = true := by decide +kernel
private theorem c1643392 : checkChunk 1643392 128 = true := by decide +kernel
private theorem c1643520 : checkChunk 1643520 128 = true := by decide +kernel
private theorem c1643648 : checkChunk 1643648 128 = true := by decide +kernel
private theorem c1643776 : checkChunk 1643776 128 = true := by decide +kernel
private theorem c1643904 : checkChunk 1643904 128 = true := by decide +kernel
private theorem c1644032 : checkChunk 1644032 128 = true := by decide +kernel
private theorem c1644160 : checkChunk 1644160 128 = true := by decide +kernel
private theorem c1644288 : checkChunk 1644288 128 = true := by decide +kernel
private theorem c1644416 : checkChunk 1644416 128 = true := by decide +kernel
private theorem c1644544 : checkChunk 1644544 128 = true := by decide +kernel
private theorem c1644672 : checkChunk 1644672 128 = true := by decide +kernel
private theorem c1644800 : checkChunk 1644800 128 = true := by decide +kernel
private theorem c1644928 : checkChunk 1644928 128 = true := by decide +kernel
private theorem c1645056 : checkChunk 1645056 128 = true := by decide +kernel
private theorem c1645184 : checkChunk 1645184 128 = true := by decide +kernel
private theorem c1645312 : checkChunk 1645312 128 = true := by decide +kernel
private theorem c1645440 : checkChunk 1645440 128 = true := by decide +kernel
private theorem c1645568 : checkChunk 1645568 128 = true := by decide +kernel
private theorem c1645696 : checkChunk 1645696 128 = true := by decide +kernel
private theorem c1645824 : checkChunk 1645824 128 = true := by decide +kernel
private theorem c1645952 : checkChunk 1645952 128 = true := by decide +kernel
private theorem c1646080 : checkChunk 1646080 128 = true := by decide +kernel
private theorem c1646208 : checkChunk 1646208 128 = true := by decide +kernel
private theorem c1646336 : checkChunk 1646336 128 = true := by decide +kernel
private theorem c1646464 : checkChunk 1646464 128 = true := by decide +kernel

public theorem checked : Checked 1638400 1646592 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1638400 128 c1638400) (checkChunk_sound 1638528 128 c1638528)) (Checked.append (checkChunk_sound 1638656 128 c1638656) (checkChunk_sound 1638784 128 c1638784))) (Checked.append (Checked.append (checkChunk_sound 1638912 128 c1638912) (checkChunk_sound 1639040 128 c1639040)) (Checked.append (checkChunk_sound 1639168 128 c1639168) (checkChunk_sound 1639296 128 c1639296)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1639424 128 c1639424) (checkChunk_sound 1639552 128 c1639552)) (Checked.append (checkChunk_sound 1639680 128 c1639680) (checkChunk_sound 1639808 128 c1639808))) (Checked.append (Checked.append (checkChunk_sound 1639936 128 c1639936) (checkChunk_sound 1640064 128 c1640064)) (Checked.append (checkChunk_sound 1640192 128 c1640192) (checkChunk_sound 1640320 128 c1640320))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1640448 128 c1640448) (checkChunk_sound 1640576 128 c1640576)) (Checked.append (checkChunk_sound 1640704 128 c1640704) (checkChunk_sound 1640832 128 c1640832))) (Checked.append (Checked.append (checkChunk_sound 1640960 128 c1640960) (checkChunk_sound 1641088 128 c1641088)) (Checked.append (checkChunk_sound 1641216 128 c1641216) (checkChunk_sound 1641344 128 c1641344)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1641472 128 c1641472) (checkChunk_sound 1641600 128 c1641600)) (Checked.append (checkChunk_sound 1641728 128 c1641728) (checkChunk_sound 1641856 128 c1641856))) (Checked.append (Checked.append (checkChunk_sound 1641984 128 c1641984) (checkChunk_sound 1642112 128 c1642112)) (Checked.append (checkChunk_sound 1642240 128 c1642240) (checkChunk_sound 1642368 128 c1642368)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1642496 128 c1642496) (checkChunk_sound 1642624 128 c1642624)) (Checked.append (checkChunk_sound 1642752 128 c1642752) (checkChunk_sound 1642880 128 c1642880))) (Checked.append (Checked.append (checkChunk_sound 1643008 128 c1643008) (checkChunk_sound 1643136 128 c1643136)) (Checked.append (checkChunk_sound 1643264 128 c1643264) (checkChunk_sound 1643392 128 c1643392)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1643520 128 c1643520) (checkChunk_sound 1643648 128 c1643648)) (Checked.append (checkChunk_sound 1643776 128 c1643776) (checkChunk_sound 1643904 128 c1643904))) (Checked.append (Checked.append (checkChunk_sound 1644032 128 c1644032) (checkChunk_sound 1644160 128 c1644160)) (Checked.append (checkChunk_sound 1644288 128 c1644288) (checkChunk_sound 1644416 128 c1644416))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1644544 128 c1644544) (checkChunk_sound 1644672 128 c1644672)) (Checked.append (checkChunk_sound 1644800 128 c1644800) (checkChunk_sound 1644928 128 c1644928))) (Checked.append (Checked.append (checkChunk_sound 1645056 128 c1645056) (checkChunk_sound 1645184 128 c1645184)) (Checked.append (checkChunk_sound 1645312 128 c1645312) (checkChunk_sound 1645440 128 c1645440)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1645568 128 c1645568) (checkChunk_sound 1645696 128 c1645696)) (Checked.append (checkChunk_sound 1645824 128 c1645824) (checkChunk_sound 1645952 128 c1645952))) (Checked.append (Checked.append (checkChunk_sound 1646080 128 c1646080) (checkChunk_sound 1646208 128 c1646208)) (Checked.append (checkChunk_sound 1646336 128 c1646336) (checkChunk_sound 1646464 128 c1646464)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B017
