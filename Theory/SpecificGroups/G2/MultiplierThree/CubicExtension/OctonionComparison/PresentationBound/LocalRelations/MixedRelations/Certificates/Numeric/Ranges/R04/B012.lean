module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [958464, 966656).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B012
private theorem c958464 : checkChunk 958464 128 = true := by decide +kernel
private theorem c958592 : checkChunk 958592 128 = true := by decide +kernel
private theorem c958720 : checkChunk 958720 128 = true := by decide +kernel
private theorem c958848 : checkChunk 958848 128 = true := by decide +kernel
private theorem c958976 : checkChunk 958976 128 = true := by decide +kernel
private theorem c959104 : checkChunk 959104 128 = true := by decide +kernel
private theorem c959232 : checkChunk 959232 128 = true := by decide +kernel
private theorem c959360 : checkChunk 959360 128 = true := by decide +kernel
private theorem c959488 : checkChunk 959488 128 = true := by decide +kernel
private theorem c959616 : checkChunk 959616 128 = true := by decide +kernel
private theorem c959744 : checkChunk 959744 128 = true := by decide +kernel
private theorem c959872 : checkChunk 959872 128 = true := by decide +kernel
private theorem c960000 : checkChunk 960000 128 = true := by decide +kernel
private theorem c960128 : checkChunk 960128 128 = true := by decide +kernel
private theorem c960256 : checkChunk 960256 128 = true := by decide +kernel
private theorem c960384 : checkChunk 960384 128 = true := by decide +kernel
private theorem c960512 : checkChunk 960512 128 = true := by decide +kernel
private theorem c960640 : checkChunk 960640 128 = true := by decide +kernel
private theorem c960768 : checkChunk 960768 128 = true := by decide +kernel
private theorem c960896 : checkChunk 960896 128 = true := by decide +kernel
private theorem c961024 : checkChunk 961024 128 = true := by decide +kernel
private theorem c961152 : checkChunk 961152 128 = true := by decide +kernel
private theorem c961280 : checkChunk 961280 128 = true := by decide +kernel
private theorem c961408 : checkChunk 961408 128 = true := by decide +kernel
private theorem c961536 : checkChunk 961536 128 = true := by decide +kernel
private theorem c961664 : checkChunk 961664 128 = true := by decide +kernel
private theorem c961792 : checkChunk 961792 128 = true := by decide +kernel
private theorem c961920 : checkChunk 961920 128 = true := by decide +kernel
private theorem c962048 : checkChunk 962048 128 = true := by decide +kernel
private theorem c962176 : checkChunk 962176 128 = true := by decide +kernel
private theorem c962304 : checkChunk 962304 128 = true := by decide +kernel
private theorem c962432 : checkChunk 962432 128 = true := by decide +kernel
private theorem c962560 : checkChunk 962560 128 = true := by decide +kernel
private theorem c962688 : checkChunk 962688 128 = true := by decide +kernel
private theorem c962816 : checkChunk 962816 128 = true := by decide +kernel
private theorem c962944 : checkChunk 962944 128 = true := by decide +kernel
private theorem c963072 : checkChunk 963072 128 = true := by decide +kernel
private theorem c963200 : checkChunk 963200 128 = true := by decide +kernel
private theorem c963328 : checkChunk 963328 128 = true := by decide +kernel
private theorem c963456 : checkChunk 963456 128 = true := by decide +kernel
private theorem c963584 : checkChunk 963584 128 = true := by decide +kernel
private theorem c963712 : checkChunk 963712 128 = true := by decide +kernel
private theorem c963840 : checkChunk 963840 128 = true := by decide +kernel
private theorem c963968 : checkChunk 963968 128 = true := by decide +kernel
private theorem c964096 : checkChunk 964096 128 = true := by decide +kernel
private theorem c964224 : checkChunk 964224 128 = true := by decide +kernel
private theorem c964352 : checkChunk 964352 128 = true := by decide +kernel
private theorem c964480 : checkChunk 964480 128 = true := by decide +kernel
private theorem c964608 : checkChunk 964608 128 = true := by decide +kernel
private theorem c964736 : checkChunk 964736 128 = true := by decide +kernel
private theorem c964864 : checkChunk 964864 128 = true := by decide +kernel
private theorem c964992 : checkChunk 964992 128 = true := by decide +kernel
private theorem c965120 : checkChunk 965120 128 = true := by decide +kernel
private theorem c965248 : checkChunk 965248 128 = true := by decide +kernel
private theorem c965376 : checkChunk 965376 128 = true := by decide +kernel
private theorem c965504 : checkChunk 965504 128 = true := by decide +kernel
private theorem c965632 : checkChunk 965632 128 = true := by decide +kernel
private theorem c965760 : checkChunk 965760 128 = true := by decide +kernel
private theorem c965888 : checkChunk 965888 128 = true := by decide +kernel
private theorem c966016 : checkChunk 966016 128 = true := by decide +kernel
private theorem c966144 : checkChunk 966144 128 = true := by decide +kernel
private theorem c966272 : checkChunk 966272 128 = true := by decide +kernel
private theorem c966400 : checkChunk 966400 128 = true := by decide +kernel
private theorem c966528 : checkChunk 966528 128 = true := by decide +kernel

public theorem checked : Checked 958464 966656 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 958464 128 c958464) (checkChunk_sound 958592 128 c958592)) (Checked.append (checkChunk_sound 958720 128 c958720) (checkChunk_sound 958848 128 c958848))) (Checked.append (Checked.append (checkChunk_sound 958976 128 c958976) (checkChunk_sound 959104 128 c959104)) (Checked.append (checkChunk_sound 959232 128 c959232) (checkChunk_sound 959360 128 c959360)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 959488 128 c959488) (checkChunk_sound 959616 128 c959616)) (Checked.append (checkChunk_sound 959744 128 c959744) (checkChunk_sound 959872 128 c959872))) (Checked.append (Checked.append (checkChunk_sound 960000 128 c960000) (checkChunk_sound 960128 128 c960128)) (Checked.append (checkChunk_sound 960256 128 c960256) (checkChunk_sound 960384 128 c960384))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 960512 128 c960512) (checkChunk_sound 960640 128 c960640)) (Checked.append (checkChunk_sound 960768 128 c960768) (checkChunk_sound 960896 128 c960896))) (Checked.append (Checked.append (checkChunk_sound 961024 128 c961024) (checkChunk_sound 961152 128 c961152)) (Checked.append (checkChunk_sound 961280 128 c961280) (checkChunk_sound 961408 128 c961408)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 961536 128 c961536) (checkChunk_sound 961664 128 c961664)) (Checked.append (checkChunk_sound 961792 128 c961792) (checkChunk_sound 961920 128 c961920))) (Checked.append (Checked.append (checkChunk_sound 962048 128 c962048) (checkChunk_sound 962176 128 c962176)) (Checked.append (checkChunk_sound 962304 128 c962304) (checkChunk_sound 962432 128 c962432)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 962560 128 c962560) (checkChunk_sound 962688 128 c962688)) (Checked.append (checkChunk_sound 962816 128 c962816) (checkChunk_sound 962944 128 c962944))) (Checked.append (Checked.append (checkChunk_sound 963072 128 c963072) (checkChunk_sound 963200 128 c963200)) (Checked.append (checkChunk_sound 963328 128 c963328) (checkChunk_sound 963456 128 c963456)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 963584 128 c963584) (checkChunk_sound 963712 128 c963712)) (Checked.append (checkChunk_sound 963840 128 c963840) (checkChunk_sound 963968 128 c963968))) (Checked.append (Checked.append (checkChunk_sound 964096 128 c964096) (checkChunk_sound 964224 128 c964224)) (Checked.append (checkChunk_sound 964352 128 c964352) (checkChunk_sound 964480 128 c964480))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 964608 128 c964608) (checkChunk_sound 964736 128 c964736)) (Checked.append (checkChunk_sound 964864 128 c964864) (checkChunk_sound 964992 128 c964992))) (Checked.append (Checked.append (checkChunk_sound 965120 128 c965120) (checkChunk_sound 965248 128 c965248)) (Checked.append (checkChunk_sound 965376 128 c965376) (checkChunk_sound 965504 128 c965504)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 965632 128 c965632) (checkChunk_sound 965760 128 c965760)) (Checked.append (checkChunk_sound 965888 128 c965888) (checkChunk_sound 966016 128 c966016))) (Checked.append (Checked.append (checkChunk_sound 966144 128 c966144) (checkChunk_sound 966272 128 c966272)) (Checked.append (checkChunk_sound 966400 128 c966400) (checkChunk_sound 966528 128 c966528)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B012
