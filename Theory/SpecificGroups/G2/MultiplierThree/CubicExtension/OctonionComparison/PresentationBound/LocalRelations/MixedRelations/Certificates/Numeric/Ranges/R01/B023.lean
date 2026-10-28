module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [409600, 417792).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B023
private theorem c409600 : checkChunk 409600 128 = true := by decide +kernel
private theorem c409728 : checkChunk 409728 128 = true := by decide +kernel
private theorem c409856 : checkChunk 409856 128 = true := by decide +kernel
private theorem c409984 : checkChunk 409984 128 = true := by decide +kernel
private theorem c410112 : checkChunk 410112 128 = true := by decide +kernel
private theorem c410240 : checkChunk 410240 128 = true := by decide +kernel
private theorem c410368 : checkChunk 410368 128 = true := by decide +kernel
private theorem c410496 : checkChunk 410496 128 = true := by decide +kernel
private theorem c410624 : checkChunk 410624 128 = true := by decide +kernel
private theorem c410752 : checkChunk 410752 128 = true := by decide +kernel
private theorem c410880 : checkChunk 410880 128 = true := by decide +kernel
private theorem c411008 : checkChunk 411008 128 = true := by decide +kernel
private theorem c411136 : checkChunk 411136 128 = true := by decide +kernel
private theorem c411264 : checkChunk 411264 128 = true := by decide +kernel
private theorem c411392 : checkChunk 411392 128 = true := by decide +kernel
private theorem c411520 : checkChunk 411520 128 = true := by decide +kernel
private theorem c411648 : checkChunk 411648 128 = true := by decide +kernel
private theorem c411776 : checkChunk 411776 128 = true := by decide +kernel
private theorem c411904 : checkChunk 411904 128 = true := by decide +kernel
private theorem c412032 : checkChunk 412032 128 = true := by decide +kernel
private theorem c412160 : checkChunk 412160 128 = true := by decide +kernel
private theorem c412288 : checkChunk 412288 128 = true := by decide +kernel
private theorem c412416 : checkChunk 412416 128 = true := by decide +kernel
private theorem c412544 : checkChunk 412544 128 = true := by decide +kernel
private theorem c412672 : checkChunk 412672 128 = true := by decide +kernel
private theorem c412800 : checkChunk 412800 128 = true := by decide +kernel
private theorem c412928 : checkChunk 412928 128 = true := by decide +kernel
private theorem c413056 : checkChunk 413056 128 = true := by decide +kernel
private theorem c413184 : checkChunk 413184 128 = true := by decide +kernel
private theorem c413312 : checkChunk 413312 128 = true := by decide +kernel
private theorem c413440 : checkChunk 413440 128 = true := by decide +kernel
private theorem c413568 : checkChunk 413568 128 = true := by decide +kernel
private theorem c413696 : checkChunk 413696 128 = true := by decide +kernel
private theorem c413824 : checkChunk 413824 128 = true := by decide +kernel
private theorem c413952 : checkChunk 413952 128 = true := by decide +kernel
private theorem c414080 : checkChunk 414080 128 = true := by decide +kernel
private theorem c414208 : checkChunk 414208 128 = true := by decide +kernel
private theorem c414336 : checkChunk 414336 128 = true := by decide +kernel
private theorem c414464 : checkChunk 414464 128 = true := by decide +kernel
private theorem c414592 : checkChunk 414592 128 = true := by decide +kernel
private theorem c414720 : checkChunk 414720 128 = true := by decide +kernel
private theorem c414848 : checkChunk 414848 128 = true := by decide +kernel
private theorem c414976 : checkChunk 414976 128 = true := by decide +kernel
private theorem c415104 : checkChunk 415104 128 = true := by decide +kernel
private theorem c415232 : checkChunk 415232 128 = true := by decide +kernel
private theorem c415360 : checkChunk 415360 128 = true := by decide +kernel
private theorem c415488 : checkChunk 415488 128 = true := by decide +kernel
private theorem c415616 : checkChunk 415616 128 = true := by decide +kernel
private theorem c415744 : checkChunk 415744 128 = true := by decide +kernel
private theorem c415872 : checkChunk 415872 128 = true := by decide +kernel
private theorem c416000 : checkChunk 416000 128 = true := by decide +kernel
private theorem c416128 : checkChunk 416128 128 = true := by decide +kernel
private theorem c416256 : checkChunk 416256 128 = true := by decide +kernel
private theorem c416384 : checkChunk 416384 128 = true := by decide +kernel
private theorem c416512 : checkChunk 416512 128 = true := by decide +kernel
private theorem c416640 : checkChunk 416640 128 = true := by decide +kernel
private theorem c416768 : checkChunk 416768 128 = true := by decide +kernel
private theorem c416896 : checkChunk 416896 128 = true := by decide +kernel
private theorem c417024 : checkChunk 417024 128 = true := by decide +kernel
private theorem c417152 : checkChunk 417152 128 = true := by decide +kernel
private theorem c417280 : checkChunk 417280 128 = true := by decide +kernel
private theorem c417408 : checkChunk 417408 128 = true := by decide +kernel
private theorem c417536 : checkChunk 417536 128 = true := by decide +kernel
private theorem c417664 : checkChunk 417664 128 = true := by decide +kernel

public theorem checked : Checked 409600 417792 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 409600 128 c409600) (checkChunk_sound 409728 128 c409728)) (Checked.append (checkChunk_sound 409856 128 c409856) (checkChunk_sound 409984 128 c409984))) (Checked.append (Checked.append (checkChunk_sound 410112 128 c410112) (checkChunk_sound 410240 128 c410240)) (Checked.append (checkChunk_sound 410368 128 c410368) (checkChunk_sound 410496 128 c410496)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 410624 128 c410624) (checkChunk_sound 410752 128 c410752)) (Checked.append (checkChunk_sound 410880 128 c410880) (checkChunk_sound 411008 128 c411008))) (Checked.append (Checked.append (checkChunk_sound 411136 128 c411136) (checkChunk_sound 411264 128 c411264)) (Checked.append (checkChunk_sound 411392 128 c411392) (checkChunk_sound 411520 128 c411520))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 411648 128 c411648) (checkChunk_sound 411776 128 c411776)) (Checked.append (checkChunk_sound 411904 128 c411904) (checkChunk_sound 412032 128 c412032))) (Checked.append (Checked.append (checkChunk_sound 412160 128 c412160) (checkChunk_sound 412288 128 c412288)) (Checked.append (checkChunk_sound 412416 128 c412416) (checkChunk_sound 412544 128 c412544)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 412672 128 c412672) (checkChunk_sound 412800 128 c412800)) (Checked.append (checkChunk_sound 412928 128 c412928) (checkChunk_sound 413056 128 c413056))) (Checked.append (Checked.append (checkChunk_sound 413184 128 c413184) (checkChunk_sound 413312 128 c413312)) (Checked.append (checkChunk_sound 413440 128 c413440) (checkChunk_sound 413568 128 c413568)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 413696 128 c413696) (checkChunk_sound 413824 128 c413824)) (Checked.append (checkChunk_sound 413952 128 c413952) (checkChunk_sound 414080 128 c414080))) (Checked.append (Checked.append (checkChunk_sound 414208 128 c414208) (checkChunk_sound 414336 128 c414336)) (Checked.append (checkChunk_sound 414464 128 c414464) (checkChunk_sound 414592 128 c414592)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 414720 128 c414720) (checkChunk_sound 414848 128 c414848)) (Checked.append (checkChunk_sound 414976 128 c414976) (checkChunk_sound 415104 128 c415104))) (Checked.append (Checked.append (checkChunk_sound 415232 128 c415232) (checkChunk_sound 415360 128 c415360)) (Checked.append (checkChunk_sound 415488 128 c415488) (checkChunk_sound 415616 128 c415616))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 415744 128 c415744) (checkChunk_sound 415872 128 c415872)) (Checked.append (checkChunk_sound 416000 128 c416000) (checkChunk_sound 416128 128 c416128))) (Checked.append (Checked.append (checkChunk_sound 416256 128 c416256) (checkChunk_sound 416384 128 c416384)) (Checked.append (checkChunk_sound 416512 128 c416512) (checkChunk_sound 416640 128 c416640)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 416768 128 c416768) (checkChunk_sound 416896 128 c416896)) (Checked.append (checkChunk_sound 417024 128 c417024) (checkChunk_sound 417152 128 c417152))) (Checked.append (Checked.append (checkChunk_sound 417280 128 c417280) (checkChunk_sound 417408 128 c417408)) (Checked.append (checkChunk_sound 417536 128 c417536) (checkChunk_sound 417664 128 c417664)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B023
