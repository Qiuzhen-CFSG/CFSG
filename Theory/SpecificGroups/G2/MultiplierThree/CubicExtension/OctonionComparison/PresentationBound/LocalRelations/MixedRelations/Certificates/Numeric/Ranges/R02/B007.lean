module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [491520, 499712).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B007
private theorem c491520 : checkChunk 491520 128 = true := by decide +kernel
private theorem c491648 : checkChunk 491648 128 = true := by decide +kernel
private theorem c491776 : checkChunk 491776 128 = true := by decide +kernel
private theorem c491904 : checkChunk 491904 128 = true := by decide +kernel
private theorem c492032 : checkChunk 492032 128 = true := by decide +kernel
private theorem c492160 : checkChunk 492160 128 = true := by decide +kernel
private theorem c492288 : checkChunk 492288 128 = true := by decide +kernel
private theorem c492416 : checkChunk 492416 128 = true := by decide +kernel
private theorem c492544 : checkChunk 492544 128 = true := by decide +kernel
private theorem c492672 : checkChunk 492672 128 = true := by decide +kernel
private theorem c492800 : checkChunk 492800 128 = true := by decide +kernel
private theorem c492928 : checkChunk 492928 128 = true := by decide +kernel
private theorem c493056 : checkChunk 493056 128 = true := by decide +kernel
private theorem c493184 : checkChunk 493184 128 = true := by decide +kernel
private theorem c493312 : checkChunk 493312 128 = true := by decide +kernel
private theorem c493440 : checkChunk 493440 128 = true := by decide +kernel
private theorem c493568 : checkChunk 493568 128 = true := by decide +kernel
private theorem c493696 : checkChunk 493696 128 = true := by decide +kernel
private theorem c493824 : checkChunk 493824 128 = true := by decide +kernel
private theorem c493952 : checkChunk 493952 128 = true := by decide +kernel
private theorem c494080 : checkChunk 494080 128 = true := by decide +kernel
private theorem c494208 : checkChunk 494208 128 = true := by decide +kernel
private theorem c494336 : checkChunk 494336 128 = true := by decide +kernel
private theorem c494464 : checkChunk 494464 128 = true := by decide +kernel
private theorem c494592 : checkChunk 494592 128 = true := by decide +kernel
private theorem c494720 : checkChunk 494720 128 = true := by decide +kernel
private theorem c494848 : checkChunk 494848 128 = true := by decide +kernel
private theorem c494976 : checkChunk 494976 128 = true := by decide +kernel
private theorem c495104 : checkChunk 495104 128 = true := by decide +kernel
private theorem c495232 : checkChunk 495232 128 = true := by decide +kernel
private theorem c495360 : checkChunk 495360 128 = true := by decide +kernel
private theorem c495488 : checkChunk 495488 128 = true := by decide +kernel
private theorem c495616 : checkChunk 495616 128 = true := by decide +kernel
private theorem c495744 : checkChunk 495744 128 = true := by decide +kernel
private theorem c495872 : checkChunk 495872 128 = true := by decide +kernel
private theorem c496000 : checkChunk 496000 128 = true := by decide +kernel
private theorem c496128 : checkChunk 496128 128 = true := by decide +kernel
private theorem c496256 : checkChunk 496256 128 = true := by decide +kernel
private theorem c496384 : checkChunk 496384 128 = true := by decide +kernel
private theorem c496512 : checkChunk 496512 128 = true := by decide +kernel
private theorem c496640 : checkChunk 496640 128 = true := by decide +kernel
private theorem c496768 : checkChunk 496768 128 = true := by decide +kernel
private theorem c496896 : checkChunk 496896 128 = true := by decide +kernel
private theorem c497024 : checkChunk 497024 128 = true := by decide +kernel
private theorem c497152 : checkChunk 497152 128 = true := by decide +kernel
private theorem c497280 : checkChunk 497280 128 = true := by decide +kernel
private theorem c497408 : checkChunk 497408 128 = true := by decide +kernel
private theorem c497536 : checkChunk 497536 128 = true := by decide +kernel
private theorem c497664 : checkChunk 497664 128 = true := by decide +kernel
private theorem c497792 : checkChunk 497792 128 = true := by decide +kernel
private theorem c497920 : checkChunk 497920 128 = true := by decide +kernel
private theorem c498048 : checkChunk 498048 128 = true := by decide +kernel
private theorem c498176 : checkChunk 498176 128 = true := by decide +kernel
private theorem c498304 : checkChunk 498304 128 = true := by decide +kernel
private theorem c498432 : checkChunk 498432 128 = true := by decide +kernel
private theorem c498560 : checkChunk 498560 128 = true := by decide +kernel
private theorem c498688 : checkChunk 498688 128 = true := by decide +kernel
private theorem c498816 : checkChunk 498816 128 = true := by decide +kernel
private theorem c498944 : checkChunk 498944 128 = true := by decide +kernel
private theorem c499072 : checkChunk 499072 128 = true := by decide +kernel
private theorem c499200 : checkChunk 499200 128 = true := by decide +kernel
private theorem c499328 : checkChunk 499328 128 = true := by decide +kernel
private theorem c499456 : checkChunk 499456 128 = true := by decide +kernel
private theorem c499584 : checkChunk 499584 128 = true := by decide +kernel

public theorem checked : Checked 491520 499712 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 491520 128 c491520) (checkChunk_sound 491648 128 c491648)) (Checked.append (checkChunk_sound 491776 128 c491776) (checkChunk_sound 491904 128 c491904))) (Checked.append (Checked.append (checkChunk_sound 492032 128 c492032) (checkChunk_sound 492160 128 c492160)) (Checked.append (checkChunk_sound 492288 128 c492288) (checkChunk_sound 492416 128 c492416)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 492544 128 c492544) (checkChunk_sound 492672 128 c492672)) (Checked.append (checkChunk_sound 492800 128 c492800) (checkChunk_sound 492928 128 c492928))) (Checked.append (Checked.append (checkChunk_sound 493056 128 c493056) (checkChunk_sound 493184 128 c493184)) (Checked.append (checkChunk_sound 493312 128 c493312) (checkChunk_sound 493440 128 c493440))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 493568 128 c493568) (checkChunk_sound 493696 128 c493696)) (Checked.append (checkChunk_sound 493824 128 c493824) (checkChunk_sound 493952 128 c493952))) (Checked.append (Checked.append (checkChunk_sound 494080 128 c494080) (checkChunk_sound 494208 128 c494208)) (Checked.append (checkChunk_sound 494336 128 c494336) (checkChunk_sound 494464 128 c494464)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 494592 128 c494592) (checkChunk_sound 494720 128 c494720)) (Checked.append (checkChunk_sound 494848 128 c494848) (checkChunk_sound 494976 128 c494976))) (Checked.append (Checked.append (checkChunk_sound 495104 128 c495104) (checkChunk_sound 495232 128 c495232)) (Checked.append (checkChunk_sound 495360 128 c495360) (checkChunk_sound 495488 128 c495488)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 495616 128 c495616) (checkChunk_sound 495744 128 c495744)) (Checked.append (checkChunk_sound 495872 128 c495872) (checkChunk_sound 496000 128 c496000))) (Checked.append (Checked.append (checkChunk_sound 496128 128 c496128) (checkChunk_sound 496256 128 c496256)) (Checked.append (checkChunk_sound 496384 128 c496384) (checkChunk_sound 496512 128 c496512)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 496640 128 c496640) (checkChunk_sound 496768 128 c496768)) (Checked.append (checkChunk_sound 496896 128 c496896) (checkChunk_sound 497024 128 c497024))) (Checked.append (Checked.append (checkChunk_sound 497152 128 c497152) (checkChunk_sound 497280 128 c497280)) (Checked.append (checkChunk_sound 497408 128 c497408) (checkChunk_sound 497536 128 c497536))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 497664 128 c497664) (checkChunk_sound 497792 128 c497792)) (Checked.append (checkChunk_sound 497920 128 c497920) (checkChunk_sound 498048 128 c498048))) (Checked.append (Checked.append (checkChunk_sound 498176 128 c498176) (checkChunk_sound 498304 128 c498304)) (Checked.append (checkChunk_sound 498432 128 c498432) (checkChunk_sound 498560 128 c498560)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 498688 128 c498688) (checkChunk_sound 498816 128 c498816)) (Checked.append (checkChunk_sound 498944 128 c498944) (checkChunk_sound 499072 128 c499072))) (Checked.append (Checked.append (checkChunk_sound 499200 128 c499200) (checkChunk_sound 499328 128 c499328)) (Checked.append (checkChunk_sound 499456 128 c499456) (checkChunk_sound 499584 128 c499584)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B007
