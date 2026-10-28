module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [663552, 671744).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B002
private theorem c663552 : checkChunk 663552 128 = true := by decide +kernel
private theorem c663680 : checkChunk 663680 128 = true := by decide +kernel
private theorem c663808 : checkChunk 663808 128 = true := by decide +kernel
private theorem c663936 : checkChunk 663936 128 = true := by decide +kernel
private theorem c664064 : checkChunk 664064 128 = true := by decide +kernel
private theorem c664192 : checkChunk 664192 128 = true := by decide +kernel
private theorem c664320 : checkChunk 664320 128 = true := by decide +kernel
private theorem c664448 : checkChunk 664448 128 = true := by decide +kernel
private theorem c664576 : checkChunk 664576 128 = true := by decide +kernel
private theorem c664704 : checkChunk 664704 128 = true := by decide +kernel
private theorem c664832 : checkChunk 664832 128 = true := by decide +kernel
private theorem c664960 : checkChunk 664960 128 = true := by decide +kernel
private theorem c665088 : checkChunk 665088 128 = true := by decide +kernel
private theorem c665216 : checkChunk 665216 128 = true := by decide +kernel
private theorem c665344 : checkChunk 665344 128 = true := by decide +kernel
private theorem c665472 : checkChunk 665472 128 = true := by decide +kernel
private theorem c665600 : checkChunk 665600 128 = true := by decide +kernel
private theorem c665728 : checkChunk 665728 128 = true := by decide +kernel
private theorem c665856 : checkChunk 665856 128 = true := by decide +kernel
private theorem c665984 : checkChunk 665984 128 = true := by decide +kernel
private theorem c666112 : checkChunk 666112 128 = true := by decide +kernel
private theorem c666240 : checkChunk 666240 128 = true := by decide +kernel
private theorem c666368 : checkChunk 666368 128 = true := by decide +kernel
private theorem c666496 : checkChunk 666496 128 = true := by decide +kernel
private theorem c666624 : checkChunk 666624 128 = true := by decide +kernel
private theorem c666752 : checkChunk 666752 128 = true := by decide +kernel
private theorem c666880 : checkChunk 666880 128 = true := by decide +kernel
private theorem c667008 : checkChunk 667008 128 = true := by decide +kernel
private theorem c667136 : checkChunk 667136 128 = true := by decide +kernel
private theorem c667264 : checkChunk 667264 128 = true := by decide +kernel
private theorem c667392 : checkChunk 667392 128 = true := by decide +kernel
private theorem c667520 : checkChunk 667520 128 = true := by decide +kernel
private theorem c667648 : checkChunk 667648 128 = true := by decide +kernel
private theorem c667776 : checkChunk 667776 128 = true := by decide +kernel
private theorem c667904 : checkChunk 667904 128 = true := by decide +kernel
private theorem c668032 : checkChunk 668032 128 = true := by decide +kernel
private theorem c668160 : checkChunk 668160 128 = true := by decide +kernel
private theorem c668288 : checkChunk 668288 128 = true := by decide +kernel
private theorem c668416 : checkChunk 668416 128 = true := by decide +kernel
private theorem c668544 : checkChunk 668544 128 = true := by decide +kernel
private theorem c668672 : checkChunk 668672 128 = true := by decide +kernel
private theorem c668800 : checkChunk 668800 128 = true := by decide +kernel
private theorem c668928 : checkChunk 668928 128 = true := by decide +kernel
private theorem c669056 : checkChunk 669056 128 = true := by decide +kernel
private theorem c669184 : checkChunk 669184 128 = true := by decide +kernel
private theorem c669312 : checkChunk 669312 128 = true := by decide +kernel
private theorem c669440 : checkChunk 669440 128 = true := by decide +kernel
private theorem c669568 : checkChunk 669568 128 = true := by decide +kernel
private theorem c669696 : checkChunk 669696 128 = true := by decide +kernel
private theorem c669824 : checkChunk 669824 128 = true := by decide +kernel
private theorem c669952 : checkChunk 669952 128 = true := by decide +kernel
private theorem c670080 : checkChunk 670080 128 = true := by decide +kernel
private theorem c670208 : checkChunk 670208 128 = true := by decide +kernel
private theorem c670336 : checkChunk 670336 128 = true := by decide +kernel
private theorem c670464 : checkChunk 670464 128 = true := by decide +kernel
private theorem c670592 : checkChunk 670592 128 = true := by decide +kernel
private theorem c670720 : checkChunk 670720 128 = true := by decide +kernel
private theorem c670848 : checkChunk 670848 128 = true := by decide +kernel
private theorem c670976 : checkChunk 670976 128 = true := by decide +kernel
private theorem c671104 : checkChunk 671104 128 = true := by decide +kernel
private theorem c671232 : checkChunk 671232 128 = true := by decide +kernel
private theorem c671360 : checkChunk 671360 128 = true := by decide +kernel
private theorem c671488 : checkChunk 671488 128 = true := by decide +kernel
private theorem c671616 : checkChunk 671616 128 = true := by decide +kernel

public theorem checked : Checked 663552 671744 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 663552 128 c663552) (checkChunk_sound 663680 128 c663680)) (Checked.append (checkChunk_sound 663808 128 c663808) (checkChunk_sound 663936 128 c663936))) (Checked.append (Checked.append (checkChunk_sound 664064 128 c664064) (checkChunk_sound 664192 128 c664192)) (Checked.append (checkChunk_sound 664320 128 c664320) (checkChunk_sound 664448 128 c664448)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 664576 128 c664576) (checkChunk_sound 664704 128 c664704)) (Checked.append (checkChunk_sound 664832 128 c664832) (checkChunk_sound 664960 128 c664960))) (Checked.append (Checked.append (checkChunk_sound 665088 128 c665088) (checkChunk_sound 665216 128 c665216)) (Checked.append (checkChunk_sound 665344 128 c665344) (checkChunk_sound 665472 128 c665472))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 665600 128 c665600) (checkChunk_sound 665728 128 c665728)) (Checked.append (checkChunk_sound 665856 128 c665856) (checkChunk_sound 665984 128 c665984))) (Checked.append (Checked.append (checkChunk_sound 666112 128 c666112) (checkChunk_sound 666240 128 c666240)) (Checked.append (checkChunk_sound 666368 128 c666368) (checkChunk_sound 666496 128 c666496)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 666624 128 c666624) (checkChunk_sound 666752 128 c666752)) (Checked.append (checkChunk_sound 666880 128 c666880) (checkChunk_sound 667008 128 c667008))) (Checked.append (Checked.append (checkChunk_sound 667136 128 c667136) (checkChunk_sound 667264 128 c667264)) (Checked.append (checkChunk_sound 667392 128 c667392) (checkChunk_sound 667520 128 c667520)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 667648 128 c667648) (checkChunk_sound 667776 128 c667776)) (Checked.append (checkChunk_sound 667904 128 c667904) (checkChunk_sound 668032 128 c668032))) (Checked.append (Checked.append (checkChunk_sound 668160 128 c668160) (checkChunk_sound 668288 128 c668288)) (Checked.append (checkChunk_sound 668416 128 c668416) (checkChunk_sound 668544 128 c668544)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 668672 128 c668672) (checkChunk_sound 668800 128 c668800)) (Checked.append (checkChunk_sound 668928 128 c668928) (checkChunk_sound 669056 128 c669056))) (Checked.append (Checked.append (checkChunk_sound 669184 128 c669184) (checkChunk_sound 669312 128 c669312)) (Checked.append (checkChunk_sound 669440 128 c669440) (checkChunk_sound 669568 128 c669568))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 669696 128 c669696) (checkChunk_sound 669824 128 c669824)) (Checked.append (checkChunk_sound 669952 128 c669952) (checkChunk_sound 670080 128 c670080))) (Checked.append (Checked.append (checkChunk_sound 670208 128 c670208) (checkChunk_sound 670336 128 c670336)) (Checked.append (checkChunk_sound 670464 128 c670464) (checkChunk_sound 670592 128 c670592)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 670720 128 c670720) (checkChunk_sound 670848 128 c670848)) (Checked.append (checkChunk_sound 670976 128 c670976) (checkChunk_sound 671104 128 c671104))) (Checked.append (Checked.append (checkChunk_sound 671232 128 c671232) (checkChunk_sound 671360 128 c671360)) (Checked.append (checkChunk_sound 671488 128 c671488) (checkChunk_sound 671616 128 c671616)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B002
