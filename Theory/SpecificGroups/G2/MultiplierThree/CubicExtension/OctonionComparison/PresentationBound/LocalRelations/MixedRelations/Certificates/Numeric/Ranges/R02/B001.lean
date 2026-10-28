module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [442368, 450560).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B001
private theorem c442368 : checkChunk 442368 128 = true := by decide +kernel
private theorem c442496 : checkChunk 442496 128 = true := by decide +kernel
private theorem c442624 : checkChunk 442624 128 = true := by decide +kernel
private theorem c442752 : checkChunk 442752 128 = true := by decide +kernel
private theorem c442880 : checkChunk 442880 128 = true := by decide +kernel
private theorem c443008 : checkChunk 443008 128 = true := by decide +kernel
private theorem c443136 : checkChunk 443136 128 = true := by decide +kernel
private theorem c443264 : checkChunk 443264 128 = true := by decide +kernel
private theorem c443392 : checkChunk 443392 128 = true := by decide +kernel
private theorem c443520 : checkChunk 443520 128 = true := by decide +kernel
private theorem c443648 : checkChunk 443648 128 = true := by decide +kernel
private theorem c443776 : checkChunk 443776 128 = true := by decide +kernel
private theorem c443904 : checkChunk 443904 128 = true := by decide +kernel
private theorem c444032 : checkChunk 444032 128 = true := by decide +kernel
private theorem c444160 : checkChunk 444160 128 = true := by decide +kernel
private theorem c444288 : checkChunk 444288 128 = true := by decide +kernel
private theorem c444416 : checkChunk 444416 128 = true := by decide +kernel
private theorem c444544 : checkChunk 444544 128 = true := by decide +kernel
private theorem c444672 : checkChunk 444672 128 = true := by decide +kernel
private theorem c444800 : checkChunk 444800 128 = true := by decide +kernel
private theorem c444928 : checkChunk 444928 128 = true := by decide +kernel
private theorem c445056 : checkChunk 445056 128 = true := by decide +kernel
private theorem c445184 : checkChunk 445184 128 = true := by decide +kernel
private theorem c445312 : checkChunk 445312 128 = true := by decide +kernel
private theorem c445440 : checkChunk 445440 128 = true := by decide +kernel
private theorem c445568 : checkChunk 445568 128 = true := by decide +kernel
private theorem c445696 : checkChunk 445696 128 = true := by decide +kernel
private theorem c445824 : checkChunk 445824 128 = true := by decide +kernel
private theorem c445952 : checkChunk 445952 128 = true := by decide +kernel
private theorem c446080 : checkChunk 446080 128 = true := by decide +kernel
private theorem c446208 : checkChunk 446208 128 = true := by decide +kernel
private theorem c446336 : checkChunk 446336 128 = true := by decide +kernel
private theorem c446464 : checkChunk 446464 128 = true := by decide +kernel
private theorem c446592 : checkChunk 446592 128 = true := by decide +kernel
private theorem c446720 : checkChunk 446720 128 = true := by decide +kernel
private theorem c446848 : checkChunk 446848 128 = true := by decide +kernel
private theorem c446976 : checkChunk 446976 128 = true := by decide +kernel
private theorem c447104 : checkChunk 447104 128 = true := by decide +kernel
private theorem c447232 : checkChunk 447232 128 = true := by decide +kernel
private theorem c447360 : checkChunk 447360 128 = true := by decide +kernel
private theorem c447488 : checkChunk 447488 128 = true := by decide +kernel
private theorem c447616 : checkChunk 447616 128 = true := by decide +kernel
private theorem c447744 : checkChunk 447744 128 = true := by decide +kernel
private theorem c447872 : checkChunk 447872 128 = true := by decide +kernel
private theorem c448000 : checkChunk 448000 128 = true := by decide +kernel
private theorem c448128 : checkChunk 448128 128 = true := by decide +kernel
private theorem c448256 : checkChunk 448256 128 = true := by decide +kernel
private theorem c448384 : checkChunk 448384 128 = true := by decide +kernel
private theorem c448512 : checkChunk 448512 128 = true := by decide +kernel
private theorem c448640 : checkChunk 448640 128 = true := by decide +kernel
private theorem c448768 : checkChunk 448768 128 = true := by decide +kernel
private theorem c448896 : checkChunk 448896 128 = true := by decide +kernel
private theorem c449024 : checkChunk 449024 128 = true := by decide +kernel
private theorem c449152 : checkChunk 449152 128 = true := by decide +kernel
private theorem c449280 : checkChunk 449280 128 = true := by decide +kernel
private theorem c449408 : checkChunk 449408 128 = true := by decide +kernel
private theorem c449536 : checkChunk 449536 128 = true := by decide +kernel
private theorem c449664 : checkChunk 449664 128 = true := by decide +kernel
private theorem c449792 : checkChunk 449792 128 = true := by decide +kernel
private theorem c449920 : checkChunk 449920 128 = true := by decide +kernel
private theorem c450048 : checkChunk 450048 128 = true := by decide +kernel
private theorem c450176 : checkChunk 450176 128 = true := by decide +kernel
private theorem c450304 : checkChunk 450304 128 = true := by decide +kernel
private theorem c450432 : checkChunk 450432 128 = true := by decide +kernel

public theorem checked : Checked 442368 450560 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 442368 128 c442368) (checkChunk_sound 442496 128 c442496)) (Checked.append (checkChunk_sound 442624 128 c442624) (checkChunk_sound 442752 128 c442752))) (Checked.append (Checked.append (checkChunk_sound 442880 128 c442880) (checkChunk_sound 443008 128 c443008)) (Checked.append (checkChunk_sound 443136 128 c443136) (checkChunk_sound 443264 128 c443264)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 443392 128 c443392) (checkChunk_sound 443520 128 c443520)) (Checked.append (checkChunk_sound 443648 128 c443648) (checkChunk_sound 443776 128 c443776))) (Checked.append (Checked.append (checkChunk_sound 443904 128 c443904) (checkChunk_sound 444032 128 c444032)) (Checked.append (checkChunk_sound 444160 128 c444160) (checkChunk_sound 444288 128 c444288))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 444416 128 c444416) (checkChunk_sound 444544 128 c444544)) (Checked.append (checkChunk_sound 444672 128 c444672) (checkChunk_sound 444800 128 c444800))) (Checked.append (Checked.append (checkChunk_sound 444928 128 c444928) (checkChunk_sound 445056 128 c445056)) (Checked.append (checkChunk_sound 445184 128 c445184) (checkChunk_sound 445312 128 c445312)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 445440 128 c445440) (checkChunk_sound 445568 128 c445568)) (Checked.append (checkChunk_sound 445696 128 c445696) (checkChunk_sound 445824 128 c445824))) (Checked.append (Checked.append (checkChunk_sound 445952 128 c445952) (checkChunk_sound 446080 128 c446080)) (Checked.append (checkChunk_sound 446208 128 c446208) (checkChunk_sound 446336 128 c446336)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 446464 128 c446464) (checkChunk_sound 446592 128 c446592)) (Checked.append (checkChunk_sound 446720 128 c446720) (checkChunk_sound 446848 128 c446848))) (Checked.append (Checked.append (checkChunk_sound 446976 128 c446976) (checkChunk_sound 447104 128 c447104)) (Checked.append (checkChunk_sound 447232 128 c447232) (checkChunk_sound 447360 128 c447360)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 447488 128 c447488) (checkChunk_sound 447616 128 c447616)) (Checked.append (checkChunk_sound 447744 128 c447744) (checkChunk_sound 447872 128 c447872))) (Checked.append (Checked.append (checkChunk_sound 448000 128 c448000) (checkChunk_sound 448128 128 c448128)) (Checked.append (checkChunk_sound 448256 128 c448256) (checkChunk_sound 448384 128 c448384))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 448512 128 c448512) (checkChunk_sound 448640 128 c448640)) (Checked.append (checkChunk_sound 448768 128 c448768) (checkChunk_sound 448896 128 c448896))) (Checked.append (Checked.append (checkChunk_sound 449024 128 c449024) (checkChunk_sound 449152 128 c449152)) (Checked.append (checkChunk_sound 449280 128 c449280) (checkChunk_sound 449408 128 c449408)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 449536 128 c449536) (checkChunk_sound 449664 128 c449664)) (Checked.append (checkChunk_sound 449792 128 c449792) (checkChunk_sound 449920 128 c449920))) (Checked.append (Checked.append (checkChunk_sound 450048 128 c450048) (checkChunk_sound 450176 128 c450176)) (Checked.append (checkChunk_sound 450304 128 c450304) (checkChunk_sound 450432 128 c450432)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B001
