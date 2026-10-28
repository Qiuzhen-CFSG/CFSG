module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [794624, 802816).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B018
private theorem c794624 : checkChunk 794624 128 = true := by decide +kernel
private theorem c794752 : checkChunk 794752 128 = true := by decide +kernel
private theorem c794880 : checkChunk 794880 128 = true := by decide +kernel
private theorem c795008 : checkChunk 795008 128 = true := by decide +kernel
private theorem c795136 : checkChunk 795136 128 = true := by decide +kernel
private theorem c795264 : checkChunk 795264 128 = true := by decide +kernel
private theorem c795392 : checkChunk 795392 128 = true := by decide +kernel
private theorem c795520 : checkChunk 795520 128 = true := by decide +kernel
private theorem c795648 : checkChunk 795648 128 = true := by decide +kernel
private theorem c795776 : checkChunk 795776 128 = true := by decide +kernel
private theorem c795904 : checkChunk 795904 128 = true := by decide +kernel
private theorem c796032 : checkChunk 796032 128 = true := by decide +kernel
private theorem c796160 : checkChunk 796160 128 = true := by decide +kernel
private theorem c796288 : checkChunk 796288 128 = true := by decide +kernel
private theorem c796416 : checkChunk 796416 128 = true := by decide +kernel
private theorem c796544 : checkChunk 796544 128 = true := by decide +kernel
private theorem c796672 : checkChunk 796672 128 = true := by decide +kernel
private theorem c796800 : checkChunk 796800 128 = true := by decide +kernel
private theorem c796928 : checkChunk 796928 128 = true := by decide +kernel
private theorem c797056 : checkChunk 797056 128 = true := by decide +kernel
private theorem c797184 : checkChunk 797184 128 = true := by decide +kernel
private theorem c797312 : checkChunk 797312 128 = true := by decide +kernel
private theorem c797440 : checkChunk 797440 128 = true := by decide +kernel
private theorem c797568 : checkChunk 797568 128 = true := by decide +kernel
private theorem c797696 : checkChunk 797696 128 = true := by decide +kernel
private theorem c797824 : checkChunk 797824 128 = true := by decide +kernel
private theorem c797952 : checkChunk 797952 128 = true := by decide +kernel
private theorem c798080 : checkChunk 798080 128 = true := by decide +kernel
private theorem c798208 : checkChunk 798208 128 = true := by decide +kernel
private theorem c798336 : checkChunk 798336 128 = true := by decide +kernel
private theorem c798464 : checkChunk 798464 128 = true := by decide +kernel
private theorem c798592 : checkChunk 798592 128 = true := by decide +kernel
private theorem c798720 : checkChunk 798720 128 = true := by decide +kernel
private theorem c798848 : checkChunk 798848 128 = true := by decide +kernel
private theorem c798976 : checkChunk 798976 128 = true := by decide +kernel
private theorem c799104 : checkChunk 799104 128 = true := by decide +kernel
private theorem c799232 : checkChunk 799232 128 = true := by decide +kernel
private theorem c799360 : checkChunk 799360 128 = true := by decide +kernel
private theorem c799488 : checkChunk 799488 128 = true := by decide +kernel
private theorem c799616 : checkChunk 799616 128 = true := by decide +kernel
private theorem c799744 : checkChunk 799744 128 = true := by decide +kernel
private theorem c799872 : checkChunk 799872 128 = true := by decide +kernel
private theorem c800000 : checkChunk 800000 128 = true := by decide +kernel
private theorem c800128 : checkChunk 800128 128 = true := by decide +kernel
private theorem c800256 : checkChunk 800256 128 = true := by decide +kernel
private theorem c800384 : checkChunk 800384 128 = true := by decide +kernel
private theorem c800512 : checkChunk 800512 128 = true := by decide +kernel
private theorem c800640 : checkChunk 800640 128 = true := by decide +kernel
private theorem c800768 : checkChunk 800768 128 = true := by decide +kernel
private theorem c800896 : checkChunk 800896 128 = true := by decide +kernel
private theorem c801024 : checkChunk 801024 128 = true := by decide +kernel
private theorem c801152 : checkChunk 801152 128 = true := by decide +kernel
private theorem c801280 : checkChunk 801280 128 = true := by decide +kernel
private theorem c801408 : checkChunk 801408 128 = true := by decide +kernel
private theorem c801536 : checkChunk 801536 128 = true := by decide +kernel
private theorem c801664 : checkChunk 801664 128 = true := by decide +kernel
private theorem c801792 : checkChunk 801792 128 = true := by decide +kernel
private theorem c801920 : checkChunk 801920 128 = true := by decide +kernel
private theorem c802048 : checkChunk 802048 128 = true := by decide +kernel
private theorem c802176 : checkChunk 802176 128 = true := by decide +kernel
private theorem c802304 : checkChunk 802304 128 = true := by decide +kernel
private theorem c802432 : checkChunk 802432 128 = true := by decide +kernel
private theorem c802560 : checkChunk 802560 128 = true := by decide +kernel
private theorem c802688 : checkChunk 802688 128 = true := by decide +kernel

public theorem checked : Checked 794624 802816 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 794624 128 c794624) (checkChunk_sound 794752 128 c794752)) (Checked.append (checkChunk_sound 794880 128 c794880) (checkChunk_sound 795008 128 c795008))) (Checked.append (Checked.append (checkChunk_sound 795136 128 c795136) (checkChunk_sound 795264 128 c795264)) (Checked.append (checkChunk_sound 795392 128 c795392) (checkChunk_sound 795520 128 c795520)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 795648 128 c795648) (checkChunk_sound 795776 128 c795776)) (Checked.append (checkChunk_sound 795904 128 c795904) (checkChunk_sound 796032 128 c796032))) (Checked.append (Checked.append (checkChunk_sound 796160 128 c796160) (checkChunk_sound 796288 128 c796288)) (Checked.append (checkChunk_sound 796416 128 c796416) (checkChunk_sound 796544 128 c796544))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 796672 128 c796672) (checkChunk_sound 796800 128 c796800)) (Checked.append (checkChunk_sound 796928 128 c796928) (checkChunk_sound 797056 128 c797056))) (Checked.append (Checked.append (checkChunk_sound 797184 128 c797184) (checkChunk_sound 797312 128 c797312)) (Checked.append (checkChunk_sound 797440 128 c797440) (checkChunk_sound 797568 128 c797568)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 797696 128 c797696) (checkChunk_sound 797824 128 c797824)) (Checked.append (checkChunk_sound 797952 128 c797952) (checkChunk_sound 798080 128 c798080))) (Checked.append (Checked.append (checkChunk_sound 798208 128 c798208) (checkChunk_sound 798336 128 c798336)) (Checked.append (checkChunk_sound 798464 128 c798464) (checkChunk_sound 798592 128 c798592)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 798720 128 c798720) (checkChunk_sound 798848 128 c798848)) (Checked.append (checkChunk_sound 798976 128 c798976) (checkChunk_sound 799104 128 c799104))) (Checked.append (Checked.append (checkChunk_sound 799232 128 c799232) (checkChunk_sound 799360 128 c799360)) (Checked.append (checkChunk_sound 799488 128 c799488) (checkChunk_sound 799616 128 c799616)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 799744 128 c799744) (checkChunk_sound 799872 128 c799872)) (Checked.append (checkChunk_sound 800000 128 c800000) (checkChunk_sound 800128 128 c800128))) (Checked.append (Checked.append (checkChunk_sound 800256 128 c800256) (checkChunk_sound 800384 128 c800384)) (Checked.append (checkChunk_sound 800512 128 c800512) (checkChunk_sound 800640 128 c800640))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 800768 128 c800768) (checkChunk_sound 800896 128 c800896)) (Checked.append (checkChunk_sound 801024 128 c801024) (checkChunk_sound 801152 128 c801152))) (Checked.append (Checked.append (checkChunk_sound 801280 128 c801280) (checkChunk_sound 801408 128 c801408)) (Checked.append (checkChunk_sound 801536 128 c801536) (checkChunk_sound 801664 128 c801664)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 801792 128 c801792) (checkChunk_sound 801920 128 c801920)) (Checked.append (checkChunk_sound 802048 128 c802048) (checkChunk_sound 802176 128 c802176))) (Checked.append (Checked.append (checkChunk_sound 802304 128 c802304) (checkChunk_sound 802432 128 c802432)) (Checked.append (checkChunk_sound 802560 128 c802560) (checkChunk_sound 802688 128 c802688)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B018
