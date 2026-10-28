module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [999424, 1007616).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B017
private theorem c999424 : checkChunk 999424 128 = true := by decide +kernel
private theorem c999552 : checkChunk 999552 128 = true := by decide +kernel
private theorem c999680 : checkChunk 999680 128 = true := by decide +kernel
private theorem c999808 : checkChunk 999808 128 = true := by decide +kernel
private theorem c999936 : checkChunk 999936 128 = true := by decide +kernel
private theorem c1000064 : checkChunk 1000064 128 = true := by decide +kernel
private theorem c1000192 : checkChunk 1000192 128 = true := by decide +kernel
private theorem c1000320 : checkChunk 1000320 128 = true := by decide +kernel
private theorem c1000448 : checkChunk 1000448 128 = true := by decide +kernel
private theorem c1000576 : checkChunk 1000576 128 = true := by decide +kernel
private theorem c1000704 : checkChunk 1000704 128 = true := by decide +kernel
private theorem c1000832 : checkChunk 1000832 128 = true := by decide +kernel
private theorem c1000960 : checkChunk 1000960 128 = true := by decide +kernel
private theorem c1001088 : checkChunk 1001088 128 = true := by decide +kernel
private theorem c1001216 : checkChunk 1001216 128 = true := by decide +kernel
private theorem c1001344 : checkChunk 1001344 128 = true := by decide +kernel
private theorem c1001472 : checkChunk 1001472 128 = true := by decide +kernel
private theorem c1001600 : checkChunk 1001600 128 = true := by decide +kernel
private theorem c1001728 : checkChunk 1001728 128 = true := by decide +kernel
private theorem c1001856 : checkChunk 1001856 128 = true := by decide +kernel
private theorem c1001984 : checkChunk 1001984 128 = true := by decide +kernel
private theorem c1002112 : checkChunk 1002112 128 = true := by decide +kernel
private theorem c1002240 : checkChunk 1002240 128 = true := by decide +kernel
private theorem c1002368 : checkChunk 1002368 128 = true := by decide +kernel
private theorem c1002496 : checkChunk 1002496 128 = true := by decide +kernel
private theorem c1002624 : checkChunk 1002624 128 = true := by decide +kernel
private theorem c1002752 : checkChunk 1002752 128 = true := by decide +kernel
private theorem c1002880 : checkChunk 1002880 128 = true := by decide +kernel
private theorem c1003008 : checkChunk 1003008 128 = true := by decide +kernel
private theorem c1003136 : checkChunk 1003136 128 = true := by decide +kernel
private theorem c1003264 : checkChunk 1003264 128 = true := by decide +kernel
private theorem c1003392 : checkChunk 1003392 128 = true := by decide +kernel
private theorem c1003520 : checkChunk 1003520 128 = true := by decide +kernel
private theorem c1003648 : checkChunk 1003648 128 = true := by decide +kernel
private theorem c1003776 : checkChunk 1003776 128 = true := by decide +kernel
private theorem c1003904 : checkChunk 1003904 128 = true := by decide +kernel
private theorem c1004032 : checkChunk 1004032 128 = true := by decide +kernel
private theorem c1004160 : checkChunk 1004160 128 = true := by decide +kernel
private theorem c1004288 : checkChunk 1004288 128 = true := by decide +kernel
private theorem c1004416 : checkChunk 1004416 128 = true := by decide +kernel
private theorem c1004544 : checkChunk 1004544 128 = true := by decide +kernel
private theorem c1004672 : checkChunk 1004672 128 = true := by decide +kernel
private theorem c1004800 : checkChunk 1004800 128 = true := by decide +kernel
private theorem c1004928 : checkChunk 1004928 128 = true := by decide +kernel
private theorem c1005056 : checkChunk 1005056 128 = true := by decide +kernel
private theorem c1005184 : checkChunk 1005184 128 = true := by decide +kernel
private theorem c1005312 : checkChunk 1005312 128 = true := by decide +kernel
private theorem c1005440 : checkChunk 1005440 128 = true := by decide +kernel
private theorem c1005568 : checkChunk 1005568 128 = true := by decide +kernel
private theorem c1005696 : checkChunk 1005696 128 = true := by decide +kernel
private theorem c1005824 : checkChunk 1005824 128 = true := by decide +kernel
private theorem c1005952 : checkChunk 1005952 128 = true := by decide +kernel
private theorem c1006080 : checkChunk 1006080 128 = true := by decide +kernel
private theorem c1006208 : checkChunk 1006208 128 = true := by decide +kernel
private theorem c1006336 : checkChunk 1006336 128 = true := by decide +kernel
private theorem c1006464 : checkChunk 1006464 128 = true := by decide +kernel
private theorem c1006592 : checkChunk 1006592 128 = true := by decide +kernel
private theorem c1006720 : checkChunk 1006720 128 = true := by decide +kernel
private theorem c1006848 : checkChunk 1006848 128 = true := by decide +kernel
private theorem c1006976 : checkChunk 1006976 128 = true := by decide +kernel
private theorem c1007104 : checkChunk 1007104 128 = true := by decide +kernel
private theorem c1007232 : checkChunk 1007232 128 = true := by decide +kernel
private theorem c1007360 : checkChunk 1007360 128 = true := by decide +kernel
private theorem c1007488 : checkChunk 1007488 128 = true := by decide +kernel

public theorem checked : Checked 999424 1007616 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 999424 128 c999424) (checkChunk_sound 999552 128 c999552)) (Checked.append (checkChunk_sound 999680 128 c999680) (checkChunk_sound 999808 128 c999808))) (Checked.append (Checked.append (checkChunk_sound 999936 128 c999936) (checkChunk_sound 1000064 128 c1000064)) (Checked.append (checkChunk_sound 1000192 128 c1000192) (checkChunk_sound 1000320 128 c1000320)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1000448 128 c1000448) (checkChunk_sound 1000576 128 c1000576)) (Checked.append (checkChunk_sound 1000704 128 c1000704) (checkChunk_sound 1000832 128 c1000832))) (Checked.append (Checked.append (checkChunk_sound 1000960 128 c1000960) (checkChunk_sound 1001088 128 c1001088)) (Checked.append (checkChunk_sound 1001216 128 c1001216) (checkChunk_sound 1001344 128 c1001344))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1001472 128 c1001472) (checkChunk_sound 1001600 128 c1001600)) (Checked.append (checkChunk_sound 1001728 128 c1001728) (checkChunk_sound 1001856 128 c1001856))) (Checked.append (Checked.append (checkChunk_sound 1001984 128 c1001984) (checkChunk_sound 1002112 128 c1002112)) (Checked.append (checkChunk_sound 1002240 128 c1002240) (checkChunk_sound 1002368 128 c1002368)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1002496 128 c1002496) (checkChunk_sound 1002624 128 c1002624)) (Checked.append (checkChunk_sound 1002752 128 c1002752) (checkChunk_sound 1002880 128 c1002880))) (Checked.append (Checked.append (checkChunk_sound 1003008 128 c1003008) (checkChunk_sound 1003136 128 c1003136)) (Checked.append (checkChunk_sound 1003264 128 c1003264) (checkChunk_sound 1003392 128 c1003392)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1003520 128 c1003520) (checkChunk_sound 1003648 128 c1003648)) (Checked.append (checkChunk_sound 1003776 128 c1003776) (checkChunk_sound 1003904 128 c1003904))) (Checked.append (Checked.append (checkChunk_sound 1004032 128 c1004032) (checkChunk_sound 1004160 128 c1004160)) (Checked.append (checkChunk_sound 1004288 128 c1004288) (checkChunk_sound 1004416 128 c1004416)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1004544 128 c1004544) (checkChunk_sound 1004672 128 c1004672)) (Checked.append (checkChunk_sound 1004800 128 c1004800) (checkChunk_sound 1004928 128 c1004928))) (Checked.append (Checked.append (checkChunk_sound 1005056 128 c1005056) (checkChunk_sound 1005184 128 c1005184)) (Checked.append (checkChunk_sound 1005312 128 c1005312) (checkChunk_sound 1005440 128 c1005440))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1005568 128 c1005568) (checkChunk_sound 1005696 128 c1005696)) (Checked.append (checkChunk_sound 1005824 128 c1005824) (checkChunk_sound 1005952 128 c1005952))) (Checked.append (Checked.append (checkChunk_sound 1006080 128 c1006080) (checkChunk_sound 1006208 128 c1006208)) (Checked.append (checkChunk_sound 1006336 128 c1006336) (checkChunk_sound 1006464 128 c1006464)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1006592 128 c1006592) (checkChunk_sound 1006720 128 c1006720)) (Checked.append (checkChunk_sound 1006848 128 c1006848) (checkChunk_sound 1006976 128 c1006976))) (Checked.append (Checked.append (checkChunk_sound 1007104 128 c1007104) (checkChunk_sound 1007232 128 c1007232)) (Checked.append (checkChunk_sound 1007360 128 c1007360) (checkChunk_sound 1007488 128 c1007488)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B017
