module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [499712, 507904).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B008
private theorem c499712 : checkChunk 499712 128 = true := by decide +kernel
private theorem c499840 : checkChunk 499840 128 = true := by decide +kernel
private theorem c499968 : checkChunk 499968 128 = true := by decide +kernel
private theorem c500096 : checkChunk 500096 128 = true := by decide +kernel
private theorem c500224 : checkChunk 500224 128 = true := by decide +kernel
private theorem c500352 : checkChunk 500352 128 = true := by decide +kernel
private theorem c500480 : checkChunk 500480 128 = true := by decide +kernel
private theorem c500608 : checkChunk 500608 128 = true := by decide +kernel
private theorem c500736 : checkChunk 500736 128 = true := by decide +kernel
private theorem c500864 : checkChunk 500864 128 = true := by decide +kernel
private theorem c500992 : checkChunk 500992 128 = true := by decide +kernel
private theorem c501120 : checkChunk 501120 128 = true := by decide +kernel
private theorem c501248 : checkChunk 501248 128 = true := by decide +kernel
private theorem c501376 : checkChunk 501376 128 = true := by decide +kernel
private theorem c501504 : checkChunk 501504 128 = true := by decide +kernel
private theorem c501632 : checkChunk 501632 128 = true := by decide +kernel
private theorem c501760 : checkChunk 501760 128 = true := by decide +kernel
private theorem c501888 : checkChunk 501888 128 = true := by decide +kernel
private theorem c502016 : checkChunk 502016 128 = true := by decide +kernel
private theorem c502144 : checkChunk 502144 128 = true := by decide +kernel
private theorem c502272 : checkChunk 502272 128 = true := by decide +kernel
private theorem c502400 : checkChunk 502400 128 = true := by decide +kernel
private theorem c502528 : checkChunk 502528 128 = true := by decide +kernel
private theorem c502656 : checkChunk 502656 128 = true := by decide +kernel
private theorem c502784 : checkChunk 502784 128 = true := by decide +kernel
private theorem c502912 : checkChunk 502912 128 = true := by decide +kernel
private theorem c503040 : checkChunk 503040 128 = true := by decide +kernel
private theorem c503168 : checkChunk 503168 128 = true := by decide +kernel
private theorem c503296 : checkChunk 503296 128 = true := by decide +kernel
private theorem c503424 : checkChunk 503424 128 = true := by decide +kernel
private theorem c503552 : checkChunk 503552 128 = true := by decide +kernel
private theorem c503680 : checkChunk 503680 128 = true := by decide +kernel
private theorem c503808 : checkChunk 503808 128 = true := by decide +kernel
private theorem c503936 : checkChunk 503936 128 = true := by decide +kernel
private theorem c504064 : checkChunk 504064 128 = true := by decide +kernel
private theorem c504192 : checkChunk 504192 128 = true := by decide +kernel
private theorem c504320 : checkChunk 504320 128 = true := by decide +kernel
private theorem c504448 : checkChunk 504448 128 = true := by decide +kernel
private theorem c504576 : checkChunk 504576 128 = true := by decide +kernel
private theorem c504704 : checkChunk 504704 128 = true := by decide +kernel
private theorem c504832 : checkChunk 504832 128 = true := by decide +kernel
private theorem c504960 : checkChunk 504960 128 = true := by decide +kernel
private theorem c505088 : checkChunk 505088 128 = true := by decide +kernel
private theorem c505216 : checkChunk 505216 128 = true := by decide +kernel
private theorem c505344 : checkChunk 505344 128 = true := by decide +kernel
private theorem c505472 : checkChunk 505472 128 = true := by decide +kernel
private theorem c505600 : checkChunk 505600 128 = true := by decide +kernel
private theorem c505728 : checkChunk 505728 128 = true := by decide +kernel
private theorem c505856 : checkChunk 505856 128 = true := by decide +kernel
private theorem c505984 : checkChunk 505984 128 = true := by decide +kernel
private theorem c506112 : checkChunk 506112 128 = true := by decide +kernel
private theorem c506240 : checkChunk 506240 128 = true := by decide +kernel
private theorem c506368 : checkChunk 506368 128 = true := by decide +kernel
private theorem c506496 : checkChunk 506496 128 = true := by decide +kernel
private theorem c506624 : checkChunk 506624 128 = true := by decide +kernel
private theorem c506752 : checkChunk 506752 128 = true := by decide +kernel
private theorem c506880 : checkChunk 506880 128 = true := by decide +kernel
private theorem c507008 : checkChunk 507008 128 = true := by decide +kernel
private theorem c507136 : checkChunk 507136 128 = true := by decide +kernel
private theorem c507264 : checkChunk 507264 128 = true := by decide +kernel
private theorem c507392 : checkChunk 507392 128 = true := by decide +kernel
private theorem c507520 : checkChunk 507520 128 = true := by decide +kernel
private theorem c507648 : checkChunk 507648 128 = true := by decide +kernel
private theorem c507776 : checkChunk 507776 128 = true := by decide +kernel

public theorem checked : Checked 499712 507904 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 499712 128 c499712) (checkChunk_sound 499840 128 c499840)) (Checked.append (checkChunk_sound 499968 128 c499968) (checkChunk_sound 500096 128 c500096))) (Checked.append (Checked.append (checkChunk_sound 500224 128 c500224) (checkChunk_sound 500352 128 c500352)) (Checked.append (checkChunk_sound 500480 128 c500480) (checkChunk_sound 500608 128 c500608)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 500736 128 c500736) (checkChunk_sound 500864 128 c500864)) (Checked.append (checkChunk_sound 500992 128 c500992) (checkChunk_sound 501120 128 c501120))) (Checked.append (Checked.append (checkChunk_sound 501248 128 c501248) (checkChunk_sound 501376 128 c501376)) (Checked.append (checkChunk_sound 501504 128 c501504) (checkChunk_sound 501632 128 c501632))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 501760 128 c501760) (checkChunk_sound 501888 128 c501888)) (Checked.append (checkChunk_sound 502016 128 c502016) (checkChunk_sound 502144 128 c502144))) (Checked.append (Checked.append (checkChunk_sound 502272 128 c502272) (checkChunk_sound 502400 128 c502400)) (Checked.append (checkChunk_sound 502528 128 c502528) (checkChunk_sound 502656 128 c502656)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 502784 128 c502784) (checkChunk_sound 502912 128 c502912)) (Checked.append (checkChunk_sound 503040 128 c503040) (checkChunk_sound 503168 128 c503168))) (Checked.append (Checked.append (checkChunk_sound 503296 128 c503296) (checkChunk_sound 503424 128 c503424)) (Checked.append (checkChunk_sound 503552 128 c503552) (checkChunk_sound 503680 128 c503680)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 503808 128 c503808) (checkChunk_sound 503936 128 c503936)) (Checked.append (checkChunk_sound 504064 128 c504064) (checkChunk_sound 504192 128 c504192))) (Checked.append (Checked.append (checkChunk_sound 504320 128 c504320) (checkChunk_sound 504448 128 c504448)) (Checked.append (checkChunk_sound 504576 128 c504576) (checkChunk_sound 504704 128 c504704)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 504832 128 c504832) (checkChunk_sound 504960 128 c504960)) (Checked.append (checkChunk_sound 505088 128 c505088) (checkChunk_sound 505216 128 c505216))) (Checked.append (Checked.append (checkChunk_sound 505344 128 c505344) (checkChunk_sound 505472 128 c505472)) (Checked.append (checkChunk_sound 505600 128 c505600) (checkChunk_sound 505728 128 c505728))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 505856 128 c505856) (checkChunk_sound 505984 128 c505984)) (Checked.append (checkChunk_sound 506112 128 c506112) (checkChunk_sound 506240 128 c506240))) (Checked.append (Checked.append (checkChunk_sound 506368 128 c506368) (checkChunk_sound 506496 128 c506496)) (Checked.append (checkChunk_sound 506624 128 c506624) (checkChunk_sound 506752 128 c506752)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 506880 128 c506880) (checkChunk_sound 507008 128 c507008)) (Checked.append (checkChunk_sound 507136 128 c507136) (checkChunk_sound 507264 128 c507264))) (Checked.append (Checked.append (checkChunk_sound 507392 128 c507392) (checkChunk_sound 507520 128 c507520)) (Checked.append (checkChunk_sound 507648 128 c507648) (checkChunk_sound 507776 128 c507776)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B008
