module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [745472, 753664).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B012
private theorem c745472 : checkChunk 745472 128 = true := by decide +kernel
private theorem c745600 : checkChunk 745600 128 = true := by decide +kernel
private theorem c745728 : checkChunk 745728 128 = true := by decide +kernel
private theorem c745856 : checkChunk 745856 128 = true := by decide +kernel
private theorem c745984 : checkChunk 745984 128 = true := by decide +kernel
private theorem c746112 : checkChunk 746112 128 = true := by decide +kernel
private theorem c746240 : checkChunk 746240 128 = true := by decide +kernel
private theorem c746368 : checkChunk 746368 128 = true := by decide +kernel
private theorem c746496 : checkChunk 746496 128 = true := by decide +kernel
private theorem c746624 : checkChunk 746624 128 = true := by decide +kernel
private theorem c746752 : checkChunk 746752 128 = true := by decide +kernel
private theorem c746880 : checkChunk 746880 128 = true := by decide +kernel
private theorem c747008 : checkChunk 747008 128 = true := by decide +kernel
private theorem c747136 : checkChunk 747136 128 = true := by decide +kernel
private theorem c747264 : checkChunk 747264 128 = true := by decide +kernel
private theorem c747392 : checkChunk 747392 128 = true := by decide +kernel
private theorem c747520 : checkChunk 747520 128 = true := by decide +kernel
private theorem c747648 : checkChunk 747648 128 = true := by decide +kernel
private theorem c747776 : checkChunk 747776 128 = true := by decide +kernel
private theorem c747904 : checkChunk 747904 128 = true := by decide +kernel
private theorem c748032 : checkChunk 748032 128 = true := by decide +kernel
private theorem c748160 : checkChunk 748160 128 = true := by decide +kernel
private theorem c748288 : checkChunk 748288 128 = true := by decide +kernel
private theorem c748416 : checkChunk 748416 128 = true := by decide +kernel
private theorem c748544 : checkChunk 748544 128 = true := by decide +kernel
private theorem c748672 : checkChunk 748672 128 = true := by decide +kernel
private theorem c748800 : checkChunk 748800 128 = true := by decide +kernel
private theorem c748928 : checkChunk 748928 128 = true := by decide +kernel
private theorem c749056 : checkChunk 749056 128 = true := by decide +kernel
private theorem c749184 : checkChunk 749184 128 = true := by decide +kernel
private theorem c749312 : checkChunk 749312 128 = true := by decide +kernel
private theorem c749440 : checkChunk 749440 128 = true := by decide +kernel
private theorem c749568 : checkChunk 749568 128 = true := by decide +kernel
private theorem c749696 : checkChunk 749696 128 = true := by decide +kernel
private theorem c749824 : checkChunk 749824 128 = true := by decide +kernel
private theorem c749952 : checkChunk 749952 128 = true := by decide +kernel
private theorem c750080 : checkChunk 750080 128 = true := by decide +kernel
private theorem c750208 : checkChunk 750208 128 = true := by decide +kernel
private theorem c750336 : checkChunk 750336 128 = true := by decide +kernel
private theorem c750464 : checkChunk 750464 128 = true := by decide +kernel
private theorem c750592 : checkChunk 750592 128 = true := by decide +kernel
private theorem c750720 : checkChunk 750720 128 = true := by decide +kernel
private theorem c750848 : checkChunk 750848 128 = true := by decide +kernel
private theorem c750976 : checkChunk 750976 128 = true := by decide +kernel
private theorem c751104 : checkChunk 751104 128 = true := by decide +kernel
private theorem c751232 : checkChunk 751232 128 = true := by decide +kernel
private theorem c751360 : checkChunk 751360 128 = true := by decide +kernel
private theorem c751488 : checkChunk 751488 128 = true := by decide +kernel
private theorem c751616 : checkChunk 751616 128 = true := by decide +kernel
private theorem c751744 : checkChunk 751744 128 = true := by decide +kernel
private theorem c751872 : checkChunk 751872 128 = true := by decide +kernel
private theorem c752000 : checkChunk 752000 128 = true := by decide +kernel
private theorem c752128 : checkChunk 752128 128 = true := by decide +kernel
private theorem c752256 : checkChunk 752256 128 = true := by decide +kernel
private theorem c752384 : checkChunk 752384 128 = true := by decide +kernel
private theorem c752512 : checkChunk 752512 128 = true := by decide +kernel
private theorem c752640 : checkChunk 752640 128 = true := by decide +kernel
private theorem c752768 : checkChunk 752768 128 = true := by decide +kernel
private theorem c752896 : checkChunk 752896 128 = true := by decide +kernel
private theorem c753024 : checkChunk 753024 128 = true := by decide +kernel
private theorem c753152 : checkChunk 753152 128 = true := by decide +kernel
private theorem c753280 : checkChunk 753280 128 = true := by decide +kernel
private theorem c753408 : checkChunk 753408 128 = true := by decide +kernel
private theorem c753536 : checkChunk 753536 128 = true := by decide +kernel

public theorem checked : Checked 745472 753664 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 745472 128 c745472) (checkChunk_sound 745600 128 c745600)) (Checked.append (checkChunk_sound 745728 128 c745728) (checkChunk_sound 745856 128 c745856))) (Checked.append (Checked.append (checkChunk_sound 745984 128 c745984) (checkChunk_sound 746112 128 c746112)) (Checked.append (checkChunk_sound 746240 128 c746240) (checkChunk_sound 746368 128 c746368)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 746496 128 c746496) (checkChunk_sound 746624 128 c746624)) (Checked.append (checkChunk_sound 746752 128 c746752) (checkChunk_sound 746880 128 c746880))) (Checked.append (Checked.append (checkChunk_sound 747008 128 c747008) (checkChunk_sound 747136 128 c747136)) (Checked.append (checkChunk_sound 747264 128 c747264) (checkChunk_sound 747392 128 c747392))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 747520 128 c747520) (checkChunk_sound 747648 128 c747648)) (Checked.append (checkChunk_sound 747776 128 c747776) (checkChunk_sound 747904 128 c747904))) (Checked.append (Checked.append (checkChunk_sound 748032 128 c748032) (checkChunk_sound 748160 128 c748160)) (Checked.append (checkChunk_sound 748288 128 c748288) (checkChunk_sound 748416 128 c748416)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 748544 128 c748544) (checkChunk_sound 748672 128 c748672)) (Checked.append (checkChunk_sound 748800 128 c748800) (checkChunk_sound 748928 128 c748928))) (Checked.append (Checked.append (checkChunk_sound 749056 128 c749056) (checkChunk_sound 749184 128 c749184)) (Checked.append (checkChunk_sound 749312 128 c749312) (checkChunk_sound 749440 128 c749440)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 749568 128 c749568) (checkChunk_sound 749696 128 c749696)) (Checked.append (checkChunk_sound 749824 128 c749824) (checkChunk_sound 749952 128 c749952))) (Checked.append (Checked.append (checkChunk_sound 750080 128 c750080) (checkChunk_sound 750208 128 c750208)) (Checked.append (checkChunk_sound 750336 128 c750336) (checkChunk_sound 750464 128 c750464)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 750592 128 c750592) (checkChunk_sound 750720 128 c750720)) (Checked.append (checkChunk_sound 750848 128 c750848) (checkChunk_sound 750976 128 c750976))) (Checked.append (Checked.append (checkChunk_sound 751104 128 c751104) (checkChunk_sound 751232 128 c751232)) (Checked.append (checkChunk_sound 751360 128 c751360) (checkChunk_sound 751488 128 c751488))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 751616 128 c751616) (checkChunk_sound 751744 128 c751744)) (Checked.append (checkChunk_sound 751872 128 c751872) (checkChunk_sound 752000 128 c752000))) (Checked.append (Checked.append (checkChunk_sound 752128 128 c752128) (checkChunk_sound 752256 128 c752256)) (Checked.append (checkChunk_sound 752384 128 c752384) (checkChunk_sound 752512 128 c752512)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 752640 128 c752640) (checkChunk_sound 752768 128 c752768)) (Checked.append (checkChunk_sound 752896 128 c752896) (checkChunk_sound 753024 128 c753024))) (Checked.append (Checked.append (checkChunk_sound 753152 128 c753152) (checkChunk_sound 753280 128 c753280)) (Checked.append (checkChunk_sound 753408 128 c753408) (checkChunk_sound 753536 128 c753536)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B012
