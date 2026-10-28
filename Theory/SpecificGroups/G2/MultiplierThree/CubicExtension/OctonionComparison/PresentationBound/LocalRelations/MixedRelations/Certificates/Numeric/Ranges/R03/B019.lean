module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [802816, 811008).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B019
private theorem c802816 : checkChunk 802816 128 = true := by decide +kernel
private theorem c802944 : checkChunk 802944 128 = true := by decide +kernel
private theorem c803072 : checkChunk 803072 128 = true := by decide +kernel
private theorem c803200 : checkChunk 803200 128 = true := by decide +kernel
private theorem c803328 : checkChunk 803328 128 = true := by decide +kernel
private theorem c803456 : checkChunk 803456 128 = true := by decide +kernel
private theorem c803584 : checkChunk 803584 128 = true := by decide +kernel
private theorem c803712 : checkChunk 803712 128 = true := by decide +kernel
private theorem c803840 : checkChunk 803840 128 = true := by decide +kernel
private theorem c803968 : checkChunk 803968 128 = true := by decide +kernel
private theorem c804096 : checkChunk 804096 128 = true := by decide +kernel
private theorem c804224 : checkChunk 804224 128 = true := by decide +kernel
private theorem c804352 : checkChunk 804352 128 = true := by decide +kernel
private theorem c804480 : checkChunk 804480 128 = true := by decide +kernel
private theorem c804608 : checkChunk 804608 128 = true := by decide +kernel
private theorem c804736 : checkChunk 804736 128 = true := by decide +kernel
private theorem c804864 : checkChunk 804864 128 = true := by decide +kernel
private theorem c804992 : checkChunk 804992 128 = true := by decide +kernel
private theorem c805120 : checkChunk 805120 128 = true := by decide +kernel
private theorem c805248 : checkChunk 805248 128 = true := by decide +kernel
private theorem c805376 : checkChunk 805376 128 = true := by decide +kernel
private theorem c805504 : checkChunk 805504 128 = true := by decide +kernel
private theorem c805632 : checkChunk 805632 128 = true := by decide +kernel
private theorem c805760 : checkChunk 805760 128 = true := by decide +kernel
private theorem c805888 : checkChunk 805888 128 = true := by decide +kernel
private theorem c806016 : checkChunk 806016 128 = true := by decide +kernel
private theorem c806144 : checkChunk 806144 128 = true := by decide +kernel
private theorem c806272 : checkChunk 806272 128 = true := by decide +kernel
private theorem c806400 : checkChunk 806400 128 = true := by decide +kernel
private theorem c806528 : checkChunk 806528 128 = true := by decide +kernel
private theorem c806656 : checkChunk 806656 128 = true := by decide +kernel
private theorem c806784 : checkChunk 806784 128 = true := by decide +kernel
private theorem c806912 : checkChunk 806912 128 = true := by decide +kernel
private theorem c807040 : checkChunk 807040 128 = true := by decide +kernel
private theorem c807168 : checkChunk 807168 128 = true := by decide +kernel
private theorem c807296 : checkChunk 807296 128 = true := by decide +kernel
private theorem c807424 : checkChunk 807424 128 = true := by decide +kernel
private theorem c807552 : checkChunk 807552 128 = true := by decide +kernel
private theorem c807680 : checkChunk 807680 128 = true := by decide +kernel
private theorem c807808 : checkChunk 807808 128 = true := by decide +kernel
private theorem c807936 : checkChunk 807936 128 = true := by decide +kernel
private theorem c808064 : checkChunk 808064 128 = true := by decide +kernel
private theorem c808192 : checkChunk 808192 128 = true := by decide +kernel
private theorem c808320 : checkChunk 808320 128 = true := by decide +kernel
private theorem c808448 : checkChunk 808448 128 = true := by decide +kernel
private theorem c808576 : checkChunk 808576 128 = true := by decide +kernel
private theorem c808704 : checkChunk 808704 128 = true := by decide +kernel
private theorem c808832 : checkChunk 808832 128 = true := by decide +kernel
private theorem c808960 : checkChunk 808960 128 = true := by decide +kernel
private theorem c809088 : checkChunk 809088 128 = true := by decide +kernel
private theorem c809216 : checkChunk 809216 128 = true := by decide +kernel
private theorem c809344 : checkChunk 809344 128 = true := by decide +kernel
private theorem c809472 : checkChunk 809472 128 = true := by decide +kernel
private theorem c809600 : checkChunk 809600 128 = true := by decide +kernel
private theorem c809728 : checkChunk 809728 128 = true := by decide +kernel
private theorem c809856 : checkChunk 809856 128 = true := by decide +kernel
private theorem c809984 : checkChunk 809984 128 = true := by decide +kernel
private theorem c810112 : checkChunk 810112 128 = true := by decide +kernel
private theorem c810240 : checkChunk 810240 128 = true := by decide +kernel
private theorem c810368 : checkChunk 810368 128 = true := by decide +kernel
private theorem c810496 : checkChunk 810496 128 = true := by decide +kernel
private theorem c810624 : checkChunk 810624 128 = true := by decide +kernel
private theorem c810752 : checkChunk 810752 128 = true := by decide +kernel
private theorem c810880 : checkChunk 810880 128 = true := by decide +kernel

public theorem checked : Checked 802816 811008 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 802816 128 c802816) (checkChunk_sound 802944 128 c802944)) (Checked.append (checkChunk_sound 803072 128 c803072) (checkChunk_sound 803200 128 c803200))) (Checked.append (Checked.append (checkChunk_sound 803328 128 c803328) (checkChunk_sound 803456 128 c803456)) (Checked.append (checkChunk_sound 803584 128 c803584) (checkChunk_sound 803712 128 c803712)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 803840 128 c803840) (checkChunk_sound 803968 128 c803968)) (Checked.append (checkChunk_sound 804096 128 c804096) (checkChunk_sound 804224 128 c804224))) (Checked.append (Checked.append (checkChunk_sound 804352 128 c804352) (checkChunk_sound 804480 128 c804480)) (Checked.append (checkChunk_sound 804608 128 c804608) (checkChunk_sound 804736 128 c804736))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 804864 128 c804864) (checkChunk_sound 804992 128 c804992)) (Checked.append (checkChunk_sound 805120 128 c805120) (checkChunk_sound 805248 128 c805248))) (Checked.append (Checked.append (checkChunk_sound 805376 128 c805376) (checkChunk_sound 805504 128 c805504)) (Checked.append (checkChunk_sound 805632 128 c805632) (checkChunk_sound 805760 128 c805760)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 805888 128 c805888) (checkChunk_sound 806016 128 c806016)) (Checked.append (checkChunk_sound 806144 128 c806144) (checkChunk_sound 806272 128 c806272))) (Checked.append (Checked.append (checkChunk_sound 806400 128 c806400) (checkChunk_sound 806528 128 c806528)) (Checked.append (checkChunk_sound 806656 128 c806656) (checkChunk_sound 806784 128 c806784)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 806912 128 c806912) (checkChunk_sound 807040 128 c807040)) (Checked.append (checkChunk_sound 807168 128 c807168) (checkChunk_sound 807296 128 c807296))) (Checked.append (Checked.append (checkChunk_sound 807424 128 c807424) (checkChunk_sound 807552 128 c807552)) (Checked.append (checkChunk_sound 807680 128 c807680) (checkChunk_sound 807808 128 c807808)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 807936 128 c807936) (checkChunk_sound 808064 128 c808064)) (Checked.append (checkChunk_sound 808192 128 c808192) (checkChunk_sound 808320 128 c808320))) (Checked.append (Checked.append (checkChunk_sound 808448 128 c808448) (checkChunk_sound 808576 128 c808576)) (Checked.append (checkChunk_sound 808704 128 c808704) (checkChunk_sound 808832 128 c808832))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 808960 128 c808960) (checkChunk_sound 809088 128 c809088)) (Checked.append (checkChunk_sound 809216 128 c809216) (checkChunk_sound 809344 128 c809344))) (Checked.append (Checked.append (checkChunk_sound 809472 128 c809472) (checkChunk_sound 809600 128 c809600)) (Checked.append (checkChunk_sound 809728 128 c809728) (checkChunk_sound 809856 128 c809856)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 809984 128 c809984) (checkChunk_sound 810112 128 c810112)) (Checked.append (checkChunk_sound 810240 128 c810240) (checkChunk_sound 810368 128 c810368))) (Checked.append (Checked.append (checkChunk_sound 810496 128 c810496) (checkChunk_sound 810624 128 c810624)) (Checked.append (checkChunk_sound 810752 128 c810752) (checkChunk_sound 810880 128 c810880)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B019
