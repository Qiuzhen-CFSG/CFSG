module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [696320, 704512).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B006
private theorem c696320 : checkChunk 696320 128 = true := by decide +kernel
private theorem c696448 : checkChunk 696448 128 = true := by decide +kernel
private theorem c696576 : checkChunk 696576 128 = true := by decide +kernel
private theorem c696704 : checkChunk 696704 128 = true := by decide +kernel
private theorem c696832 : checkChunk 696832 128 = true := by decide +kernel
private theorem c696960 : checkChunk 696960 128 = true := by decide +kernel
private theorem c697088 : checkChunk 697088 128 = true := by decide +kernel
private theorem c697216 : checkChunk 697216 128 = true := by decide +kernel
private theorem c697344 : checkChunk 697344 128 = true := by decide +kernel
private theorem c697472 : checkChunk 697472 128 = true := by decide +kernel
private theorem c697600 : checkChunk 697600 128 = true := by decide +kernel
private theorem c697728 : checkChunk 697728 128 = true := by decide +kernel
private theorem c697856 : checkChunk 697856 128 = true := by decide +kernel
private theorem c697984 : checkChunk 697984 128 = true := by decide +kernel
private theorem c698112 : checkChunk 698112 128 = true := by decide +kernel
private theorem c698240 : checkChunk 698240 128 = true := by decide +kernel
private theorem c698368 : checkChunk 698368 128 = true := by decide +kernel
private theorem c698496 : checkChunk 698496 128 = true := by decide +kernel
private theorem c698624 : checkChunk 698624 128 = true := by decide +kernel
private theorem c698752 : checkChunk 698752 128 = true := by decide +kernel
private theorem c698880 : checkChunk 698880 128 = true := by decide +kernel
private theorem c699008 : checkChunk 699008 128 = true := by decide +kernel
private theorem c699136 : checkChunk 699136 128 = true := by decide +kernel
private theorem c699264 : checkChunk 699264 128 = true := by decide +kernel
private theorem c699392 : checkChunk 699392 128 = true := by decide +kernel
private theorem c699520 : checkChunk 699520 128 = true := by decide +kernel
private theorem c699648 : checkChunk 699648 128 = true := by decide +kernel
private theorem c699776 : checkChunk 699776 128 = true := by decide +kernel
private theorem c699904 : checkChunk 699904 128 = true := by decide +kernel
private theorem c700032 : checkChunk 700032 128 = true := by decide +kernel
private theorem c700160 : checkChunk 700160 128 = true := by decide +kernel
private theorem c700288 : checkChunk 700288 128 = true := by decide +kernel
private theorem c700416 : checkChunk 700416 128 = true := by decide +kernel
private theorem c700544 : checkChunk 700544 128 = true := by decide +kernel
private theorem c700672 : checkChunk 700672 128 = true := by decide +kernel
private theorem c700800 : checkChunk 700800 128 = true := by decide +kernel
private theorem c700928 : checkChunk 700928 128 = true := by decide +kernel
private theorem c701056 : checkChunk 701056 128 = true := by decide +kernel
private theorem c701184 : checkChunk 701184 128 = true := by decide +kernel
private theorem c701312 : checkChunk 701312 128 = true := by decide +kernel
private theorem c701440 : checkChunk 701440 128 = true := by decide +kernel
private theorem c701568 : checkChunk 701568 128 = true := by decide +kernel
private theorem c701696 : checkChunk 701696 128 = true := by decide +kernel
private theorem c701824 : checkChunk 701824 128 = true := by decide +kernel
private theorem c701952 : checkChunk 701952 128 = true := by decide +kernel
private theorem c702080 : checkChunk 702080 128 = true := by decide +kernel
private theorem c702208 : checkChunk 702208 128 = true := by decide +kernel
private theorem c702336 : checkChunk 702336 128 = true := by decide +kernel
private theorem c702464 : checkChunk 702464 128 = true := by decide +kernel
private theorem c702592 : checkChunk 702592 128 = true := by decide +kernel
private theorem c702720 : checkChunk 702720 128 = true := by decide +kernel
private theorem c702848 : checkChunk 702848 128 = true := by decide +kernel
private theorem c702976 : checkChunk 702976 128 = true := by decide +kernel
private theorem c703104 : checkChunk 703104 128 = true := by decide +kernel
private theorem c703232 : checkChunk 703232 128 = true := by decide +kernel
private theorem c703360 : checkChunk 703360 128 = true := by decide +kernel
private theorem c703488 : checkChunk 703488 128 = true := by decide +kernel
private theorem c703616 : checkChunk 703616 128 = true := by decide +kernel
private theorem c703744 : checkChunk 703744 128 = true := by decide +kernel
private theorem c703872 : checkChunk 703872 128 = true := by decide +kernel
private theorem c704000 : checkChunk 704000 128 = true := by decide +kernel
private theorem c704128 : checkChunk 704128 128 = true := by decide +kernel
private theorem c704256 : checkChunk 704256 128 = true := by decide +kernel
private theorem c704384 : checkChunk 704384 128 = true := by decide +kernel

public theorem checked : Checked 696320 704512 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 696320 128 c696320) (checkChunk_sound 696448 128 c696448)) (Checked.append (checkChunk_sound 696576 128 c696576) (checkChunk_sound 696704 128 c696704))) (Checked.append (Checked.append (checkChunk_sound 696832 128 c696832) (checkChunk_sound 696960 128 c696960)) (Checked.append (checkChunk_sound 697088 128 c697088) (checkChunk_sound 697216 128 c697216)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 697344 128 c697344) (checkChunk_sound 697472 128 c697472)) (Checked.append (checkChunk_sound 697600 128 c697600) (checkChunk_sound 697728 128 c697728))) (Checked.append (Checked.append (checkChunk_sound 697856 128 c697856) (checkChunk_sound 697984 128 c697984)) (Checked.append (checkChunk_sound 698112 128 c698112) (checkChunk_sound 698240 128 c698240))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 698368 128 c698368) (checkChunk_sound 698496 128 c698496)) (Checked.append (checkChunk_sound 698624 128 c698624) (checkChunk_sound 698752 128 c698752))) (Checked.append (Checked.append (checkChunk_sound 698880 128 c698880) (checkChunk_sound 699008 128 c699008)) (Checked.append (checkChunk_sound 699136 128 c699136) (checkChunk_sound 699264 128 c699264)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 699392 128 c699392) (checkChunk_sound 699520 128 c699520)) (Checked.append (checkChunk_sound 699648 128 c699648) (checkChunk_sound 699776 128 c699776))) (Checked.append (Checked.append (checkChunk_sound 699904 128 c699904) (checkChunk_sound 700032 128 c700032)) (Checked.append (checkChunk_sound 700160 128 c700160) (checkChunk_sound 700288 128 c700288)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 700416 128 c700416) (checkChunk_sound 700544 128 c700544)) (Checked.append (checkChunk_sound 700672 128 c700672) (checkChunk_sound 700800 128 c700800))) (Checked.append (Checked.append (checkChunk_sound 700928 128 c700928) (checkChunk_sound 701056 128 c701056)) (Checked.append (checkChunk_sound 701184 128 c701184) (checkChunk_sound 701312 128 c701312)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 701440 128 c701440) (checkChunk_sound 701568 128 c701568)) (Checked.append (checkChunk_sound 701696 128 c701696) (checkChunk_sound 701824 128 c701824))) (Checked.append (Checked.append (checkChunk_sound 701952 128 c701952) (checkChunk_sound 702080 128 c702080)) (Checked.append (checkChunk_sound 702208 128 c702208) (checkChunk_sound 702336 128 c702336))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 702464 128 c702464) (checkChunk_sound 702592 128 c702592)) (Checked.append (checkChunk_sound 702720 128 c702720) (checkChunk_sound 702848 128 c702848))) (Checked.append (Checked.append (checkChunk_sound 702976 128 c702976) (checkChunk_sound 703104 128 c703104)) (Checked.append (checkChunk_sound 703232 128 c703232) (checkChunk_sound 703360 128 c703360)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 703488 128 c703488) (checkChunk_sound 703616 128 c703616)) (Checked.append (checkChunk_sound 703744 128 c703744) (checkChunk_sound 703872 128 c703872))) (Checked.append (Checked.append (checkChunk_sound 704000 128 c704000) (checkChunk_sound 704128 128 c704128)) (Checked.append (checkChunk_sound 704256 128 c704256) (checkChunk_sound 704384 128 c704384)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B006
