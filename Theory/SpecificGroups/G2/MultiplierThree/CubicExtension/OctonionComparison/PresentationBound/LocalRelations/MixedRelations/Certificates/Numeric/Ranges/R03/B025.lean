module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [851968, 860160).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B025
private theorem c851968 : checkChunk 851968 128 = true := by decide +kernel
private theorem c852096 : checkChunk 852096 128 = true := by decide +kernel
private theorem c852224 : checkChunk 852224 128 = true := by decide +kernel
private theorem c852352 : checkChunk 852352 128 = true := by decide +kernel
private theorem c852480 : checkChunk 852480 128 = true := by decide +kernel
private theorem c852608 : checkChunk 852608 128 = true := by decide +kernel
private theorem c852736 : checkChunk 852736 128 = true := by decide +kernel
private theorem c852864 : checkChunk 852864 128 = true := by decide +kernel
private theorem c852992 : checkChunk 852992 128 = true := by decide +kernel
private theorem c853120 : checkChunk 853120 128 = true := by decide +kernel
private theorem c853248 : checkChunk 853248 128 = true := by decide +kernel
private theorem c853376 : checkChunk 853376 128 = true := by decide +kernel
private theorem c853504 : checkChunk 853504 128 = true := by decide +kernel
private theorem c853632 : checkChunk 853632 128 = true := by decide +kernel
private theorem c853760 : checkChunk 853760 128 = true := by decide +kernel
private theorem c853888 : checkChunk 853888 128 = true := by decide +kernel
private theorem c854016 : checkChunk 854016 128 = true := by decide +kernel
private theorem c854144 : checkChunk 854144 128 = true := by decide +kernel
private theorem c854272 : checkChunk 854272 128 = true := by decide +kernel
private theorem c854400 : checkChunk 854400 128 = true := by decide +kernel
private theorem c854528 : checkChunk 854528 128 = true := by decide +kernel
private theorem c854656 : checkChunk 854656 128 = true := by decide +kernel
private theorem c854784 : checkChunk 854784 128 = true := by decide +kernel
private theorem c854912 : checkChunk 854912 128 = true := by decide +kernel
private theorem c855040 : checkChunk 855040 128 = true := by decide +kernel
private theorem c855168 : checkChunk 855168 128 = true := by decide +kernel
private theorem c855296 : checkChunk 855296 128 = true := by decide +kernel
private theorem c855424 : checkChunk 855424 128 = true := by decide +kernel
private theorem c855552 : checkChunk 855552 128 = true := by decide +kernel
private theorem c855680 : checkChunk 855680 128 = true := by decide +kernel
private theorem c855808 : checkChunk 855808 128 = true := by decide +kernel
private theorem c855936 : checkChunk 855936 128 = true := by decide +kernel
private theorem c856064 : checkChunk 856064 128 = true := by decide +kernel
private theorem c856192 : checkChunk 856192 128 = true := by decide +kernel
private theorem c856320 : checkChunk 856320 128 = true := by decide +kernel
private theorem c856448 : checkChunk 856448 128 = true := by decide +kernel
private theorem c856576 : checkChunk 856576 128 = true := by decide +kernel
private theorem c856704 : checkChunk 856704 128 = true := by decide +kernel
private theorem c856832 : checkChunk 856832 128 = true := by decide +kernel
private theorem c856960 : checkChunk 856960 128 = true := by decide +kernel
private theorem c857088 : checkChunk 857088 128 = true := by decide +kernel
private theorem c857216 : checkChunk 857216 128 = true := by decide +kernel
private theorem c857344 : checkChunk 857344 128 = true := by decide +kernel
private theorem c857472 : checkChunk 857472 128 = true := by decide +kernel
private theorem c857600 : checkChunk 857600 128 = true := by decide +kernel
private theorem c857728 : checkChunk 857728 128 = true := by decide +kernel
private theorem c857856 : checkChunk 857856 128 = true := by decide +kernel
private theorem c857984 : checkChunk 857984 128 = true := by decide +kernel
private theorem c858112 : checkChunk 858112 128 = true := by decide +kernel
private theorem c858240 : checkChunk 858240 128 = true := by decide +kernel
private theorem c858368 : checkChunk 858368 128 = true := by decide +kernel
private theorem c858496 : checkChunk 858496 128 = true := by decide +kernel
private theorem c858624 : checkChunk 858624 128 = true := by decide +kernel
private theorem c858752 : checkChunk 858752 128 = true := by decide +kernel
private theorem c858880 : checkChunk 858880 128 = true := by decide +kernel
private theorem c859008 : checkChunk 859008 128 = true := by decide +kernel
private theorem c859136 : checkChunk 859136 128 = true := by decide +kernel
private theorem c859264 : checkChunk 859264 128 = true := by decide +kernel
private theorem c859392 : checkChunk 859392 128 = true := by decide +kernel
private theorem c859520 : checkChunk 859520 128 = true := by decide +kernel
private theorem c859648 : checkChunk 859648 128 = true := by decide +kernel
private theorem c859776 : checkChunk 859776 128 = true := by decide +kernel
private theorem c859904 : checkChunk 859904 128 = true := by decide +kernel
private theorem c860032 : checkChunk 860032 128 = true := by decide +kernel

public theorem checked : Checked 851968 860160 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 851968 128 c851968) (checkChunk_sound 852096 128 c852096)) (Checked.append (checkChunk_sound 852224 128 c852224) (checkChunk_sound 852352 128 c852352))) (Checked.append (Checked.append (checkChunk_sound 852480 128 c852480) (checkChunk_sound 852608 128 c852608)) (Checked.append (checkChunk_sound 852736 128 c852736) (checkChunk_sound 852864 128 c852864)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 852992 128 c852992) (checkChunk_sound 853120 128 c853120)) (Checked.append (checkChunk_sound 853248 128 c853248) (checkChunk_sound 853376 128 c853376))) (Checked.append (Checked.append (checkChunk_sound 853504 128 c853504) (checkChunk_sound 853632 128 c853632)) (Checked.append (checkChunk_sound 853760 128 c853760) (checkChunk_sound 853888 128 c853888))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 854016 128 c854016) (checkChunk_sound 854144 128 c854144)) (Checked.append (checkChunk_sound 854272 128 c854272) (checkChunk_sound 854400 128 c854400))) (Checked.append (Checked.append (checkChunk_sound 854528 128 c854528) (checkChunk_sound 854656 128 c854656)) (Checked.append (checkChunk_sound 854784 128 c854784) (checkChunk_sound 854912 128 c854912)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 855040 128 c855040) (checkChunk_sound 855168 128 c855168)) (Checked.append (checkChunk_sound 855296 128 c855296) (checkChunk_sound 855424 128 c855424))) (Checked.append (Checked.append (checkChunk_sound 855552 128 c855552) (checkChunk_sound 855680 128 c855680)) (Checked.append (checkChunk_sound 855808 128 c855808) (checkChunk_sound 855936 128 c855936)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 856064 128 c856064) (checkChunk_sound 856192 128 c856192)) (Checked.append (checkChunk_sound 856320 128 c856320) (checkChunk_sound 856448 128 c856448))) (Checked.append (Checked.append (checkChunk_sound 856576 128 c856576) (checkChunk_sound 856704 128 c856704)) (Checked.append (checkChunk_sound 856832 128 c856832) (checkChunk_sound 856960 128 c856960)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 857088 128 c857088) (checkChunk_sound 857216 128 c857216)) (Checked.append (checkChunk_sound 857344 128 c857344) (checkChunk_sound 857472 128 c857472))) (Checked.append (Checked.append (checkChunk_sound 857600 128 c857600) (checkChunk_sound 857728 128 c857728)) (Checked.append (checkChunk_sound 857856 128 c857856) (checkChunk_sound 857984 128 c857984))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 858112 128 c858112) (checkChunk_sound 858240 128 c858240)) (Checked.append (checkChunk_sound 858368 128 c858368) (checkChunk_sound 858496 128 c858496))) (Checked.append (Checked.append (checkChunk_sound 858624 128 c858624) (checkChunk_sound 858752 128 c858752)) (Checked.append (checkChunk_sound 858880 128 c858880) (checkChunk_sound 859008 128 c859008)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 859136 128 c859136) (checkChunk_sound 859264 128 c859264)) (Checked.append (checkChunk_sound 859392 128 c859392) (checkChunk_sound 859520 128 c859520))) (Checked.append (Checked.append (checkChunk_sound 859648 128 c859648) (checkChunk_sound 859776 128 c859776)) (Checked.append (checkChunk_sound 859904 128 c859904) (checkChunk_sound 860032 128 c860032)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B025
