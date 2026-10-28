module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [24576, 32768).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B002
private theorem c24576 : checkChunk 24576 128 = true := by decide +kernel
private theorem c24704 : checkChunk 24704 128 = true := by decide +kernel
private theorem c24832 : checkChunk 24832 128 = true := by decide +kernel
private theorem c24960 : checkChunk 24960 128 = true := by decide +kernel
private theorem c25088 : checkChunk 25088 128 = true := by decide +kernel
private theorem c25216 : checkChunk 25216 128 = true := by decide +kernel
private theorem c25344 : checkChunk 25344 128 = true := by decide +kernel
private theorem c25472 : checkChunk 25472 128 = true := by decide +kernel
private theorem c25600 : checkChunk 25600 128 = true := by decide +kernel
private theorem c25728 : checkChunk 25728 128 = true := by decide +kernel
private theorem c25856 : checkChunk 25856 128 = true := by decide +kernel
private theorem c25984 : checkChunk 25984 128 = true := by decide +kernel
private theorem c26112 : checkChunk 26112 128 = true := by decide +kernel
private theorem c26240 : checkChunk 26240 128 = true := by decide +kernel
private theorem c26368 : checkChunk 26368 128 = true := by decide +kernel
private theorem c26496 : checkChunk 26496 128 = true := by decide +kernel
private theorem c26624 : checkChunk 26624 128 = true := by decide +kernel
private theorem c26752 : checkChunk 26752 128 = true := by decide +kernel
private theorem c26880 : checkChunk 26880 128 = true := by decide +kernel
private theorem c27008 : checkChunk 27008 128 = true := by decide +kernel
private theorem c27136 : checkChunk 27136 128 = true := by decide +kernel
private theorem c27264 : checkChunk 27264 128 = true := by decide +kernel
private theorem c27392 : checkChunk 27392 128 = true := by decide +kernel
private theorem c27520 : checkChunk 27520 128 = true := by decide +kernel
private theorem c27648 : checkChunk 27648 128 = true := by decide +kernel
private theorem c27776 : checkChunk 27776 128 = true := by decide +kernel
private theorem c27904 : checkChunk 27904 128 = true := by decide +kernel
private theorem c28032 : checkChunk 28032 128 = true := by decide +kernel
private theorem c28160 : checkChunk 28160 128 = true := by decide +kernel
private theorem c28288 : checkChunk 28288 128 = true := by decide +kernel
private theorem c28416 : checkChunk 28416 128 = true := by decide +kernel
private theorem c28544 : checkChunk 28544 128 = true := by decide +kernel
private theorem c28672 : checkChunk 28672 128 = true := by decide +kernel
private theorem c28800 : checkChunk 28800 128 = true := by decide +kernel
private theorem c28928 : checkChunk 28928 128 = true := by decide +kernel
private theorem c29056 : checkChunk 29056 128 = true := by decide +kernel
private theorem c29184 : checkChunk 29184 128 = true := by decide +kernel
private theorem c29312 : checkChunk 29312 128 = true := by decide +kernel
private theorem c29440 : checkChunk 29440 128 = true := by decide +kernel
private theorem c29568 : checkChunk 29568 128 = true := by decide +kernel
private theorem c29696 : checkChunk 29696 128 = true := by decide +kernel
private theorem c29824 : checkChunk 29824 128 = true := by decide +kernel
private theorem c29952 : checkChunk 29952 128 = true := by decide +kernel
private theorem c30080 : checkChunk 30080 128 = true := by decide +kernel
private theorem c30208 : checkChunk 30208 128 = true := by decide +kernel
private theorem c30336 : checkChunk 30336 128 = true := by decide +kernel
private theorem c30464 : checkChunk 30464 128 = true := by decide +kernel
private theorem c30592 : checkChunk 30592 128 = true := by decide +kernel
private theorem c30720 : checkChunk 30720 128 = true := by decide +kernel
private theorem c30848 : checkChunk 30848 128 = true := by decide +kernel
private theorem c30976 : checkChunk 30976 128 = true := by decide +kernel
private theorem c31104 : checkChunk 31104 128 = true := by decide +kernel
private theorem c31232 : checkChunk 31232 128 = true := by decide +kernel
private theorem c31360 : checkChunk 31360 128 = true := by decide +kernel
private theorem c31488 : checkChunk 31488 128 = true := by decide +kernel
private theorem c31616 : checkChunk 31616 128 = true := by decide +kernel
private theorem c31744 : checkChunk 31744 128 = true := by decide +kernel
private theorem c31872 : checkChunk 31872 128 = true := by decide +kernel
private theorem c32000 : checkChunk 32000 128 = true := by decide +kernel
private theorem c32128 : checkChunk 32128 128 = true := by decide +kernel
private theorem c32256 : checkChunk 32256 128 = true := by decide +kernel
private theorem c32384 : checkChunk 32384 128 = true := by decide +kernel
private theorem c32512 : checkChunk 32512 128 = true := by decide +kernel
private theorem c32640 : checkChunk 32640 128 = true := by decide +kernel

public theorem checked : Checked 24576 32768 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 24576 128 c24576) (checkChunk_sound 24704 128 c24704)) (Checked.append (checkChunk_sound 24832 128 c24832) (checkChunk_sound 24960 128 c24960))) (Checked.append (Checked.append (checkChunk_sound 25088 128 c25088) (checkChunk_sound 25216 128 c25216)) (Checked.append (checkChunk_sound 25344 128 c25344) (checkChunk_sound 25472 128 c25472)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 25600 128 c25600) (checkChunk_sound 25728 128 c25728)) (Checked.append (checkChunk_sound 25856 128 c25856) (checkChunk_sound 25984 128 c25984))) (Checked.append (Checked.append (checkChunk_sound 26112 128 c26112) (checkChunk_sound 26240 128 c26240)) (Checked.append (checkChunk_sound 26368 128 c26368) (checkChunk_sound 26496 128 c26496))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 26624 128 c26624) (checkChunk_sound 26752 128 c26752)) (Checked.append (checkChunk_sound 26880 128 c26880) (checkChunk_sound 27008 128 c27008))) (Checked.append (Checked.append (checkChunk_sound 27136 128 c27136) (checkChunk_sound 27264 128 c27264)) (Checked.append (checkChunk_sound 27392 128 c27392) (checkChunk_sound 27520 128 c27520)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 27648 128 c27648) (checkChunk_sound 27776 128 c27776)) (Checked.append (checkChunk_sound 27904 128 c27904) (checkChunk_sound 28032 128 c28032))) (Checked.append (Checked.append (checkChunk_sound 28160 128 c28160) (checkChunk_sound 28288 128 c28288)) (Checked.append (checkChunk_sound 28416 128 c28416) (checkChunk_sound 28544 128 c28544)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 28672 128 c28672) (checkChunk_sound 28800 128 c28800)) (Checked.append (checkChunk_sound 28928 128 c28928) (checkChunk_sound 29056 128 c29056))) (Checked.append (Checked.append (checkChunk_sound 29184 128 c29184) (checkChunk_sound 29312 128 c29312)) (Checked.append (checkChunk_sound 29440 128 c29440) (checkChunk_sound 29568 128 c29568)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 29696 128 c29696) (checkChunk_sound 29824 128 c29824)) (Checked.append (checkChunk_sound 29952 128 c29952) (checkChunk_sound 30080 128 c30080))) (Checked.append (Checked.append (checkChunk_sound 30208 128 c30208) (checkChunk_sound 30336 128 c30336)) (Checked.append (checkChunk_sound 30464 128 c30464) (checkChunk_sound 30592 128 c30592))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 30720 128 c30720) (checkChunk_sound 30848 128 c30848)) (Checked.append (checkChunk_sound 30976 128 c30976) (checkChunk_sound 31104 128 c31104))) (Checked.append (Checked.append (checkChunk_sound 31232 128 c31232) (checkChunk_sound 31360 128 c31360)) (Checked.append (checkChunk_sound 31488 128 c31488) (checkChunk_sound 31616 128 c31616)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 31744 128 c31744) (checkChunk_sound 31872 128 c31872)) (Checked.append (checkChunk_sound 32000 128 c32000) (checkChunk_sound 32128 128 c32128))) (Checked.append (Checked.append (checkChunk_sound 32256 128 c32256) (checkChunk_sound 32384 128 c32384)) (Checked.append (checkChunk_sound 32512 128 c32512) (checkChunk_sound 32640 128 c32640)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B002
