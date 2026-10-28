module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [573440, 581632).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B017
private theorem c573440 : checkChunk 573440 128 = true := by decide +kernel
private theorem c573568 : checkChunk 573568 128 = true := by decide +kernel
private theorem c573696 : checkChunk 573696 128 = true := by decide +kernel
private theorem c573824 : checkChunk 573824 128 = true := by decide +kernel
private theorem c573952 : checkChunk 573952 128 = true := by decide +kernel
private theorem c574080 : checkChunk 574080 128 = true := by decide +kernel
private theorem c574208 : checkChunk 574208 128 = true := by decide +kernel
private theorem c574336 : checkChunk 574336 128 = true := by decide +kernel
private theorem c574464 : checkChunk 574464 128 = true := by decide +kernel
private theorem c574592 : checkChunk 574592 128 = true := by decide +kernel
private theorem c574720 : checkChunk 574720 128 = true := by decide +kernel
private theorem c574848 : checkChunk 574848 128 = true := by decide +kernel
private theorem c574976 : checkChunk 574976 128 = true := by decide +kernel
private theorem c575104 : checkChunk 575104 128 = true := by decide +kernel
private theorem c575232 : checkChunk 575232 128 = true := by decide +kernel
private theorem c575360 : checkChunk 575360 128 = true := by decide +kernel
private theorem c575488 : checkChunk 575488 128 = true := by decide +kernel
private theorem c575616 : checkChunk 575616 128 = true := by decide +kernel
private theorem c575744 : checkChunk 575744 128 = true := by decide +kernel
private theorem c575872 : checkChunk 575872 128 = true := by decide +kernel
private theorem c576000 : checkChunk 576000 128 = true := by decide +kernel
private theorem c576128 : checkChunk 576128 128 = true := by decide +kernel
private theorem c576256 : checkChunk 576256 128 = true := by decide +kernel
private theorem c576384 : checkChunk 576384 128 = true := by decide +kernel
private theorem c576512 : checkChunk 576512 128 = true := by decide +kernel
private theorem c576640 : checkChunk 576640 128 = true := by decide +kernel
private theorem c576768 : checkChunk 576768 128 = true := by decide +kernel
private theorem c576896 : checkChunk 576896 128 = true := by decide +kernel
private theorem c577024 : checkChunk 577024 128 = true := by decide +kernel
private theorem c577152 : checkChunk 577152 128 = true := by decide +kernel
private theorem c577280 : checkChunk 577280 128 = true := by decide +kernel
private theorem c577408 : checkChunk 577408 128 = true := by decide +kernel
private theorem c577536 : checkChunk 577536 128 = true := by decide +kernel
private theorem c577664 : checkChunk 577664 128 = true := by decide +kernel
private theorem c577792 : checkChunk 577792 128 = true := by decide +kernel
private theorem c577920 : checkChunk 577920 128 = true := by decide +kernel
private theorem c578048 : checkChunk 578048 128 = true := by decide +kernel
private theorem c578176 : checkChunk 578176 128 = true := by decide +kernel
private theorem c578304 : checkChunk 578304 128 = true := by decide +kernel
private theorem c578432 : checkChunk 578432 128 = true := by decide +kernel
private theorem c578560 : checkChunk 578560 128 = true := by decide +kernel
private theorem c578688 : checkChunk 578688 128 = true := by decide +kernel
private theorem c578816 : checkChunk 578816 128 = true := by decide +kernel
private theorem c578944 : checkChunk 578944 128 = true := by decide +kernel
private theorem c579072 : checkChunk 579072 128 = true := by decide +kernel
private theorem c579200 : checkChunk 579200 128 = true := by decide +kernel
private theorem c579328 : checkChunk 579328 128 = true := by decide +kernel
private theorem c579456 : checkChunk 579456 128 = true := by decide +kernel
private theorem c579584 : checkChunk 579584 128 = true := by decide +kernel
private theorem c579712 : checkChunk 579712 128 = true := by decide +kernel
private theorem c579840 : checkChunk 579840 128 = true := by decide +kernel
private theorem c579968 : checkChunk 579968 128 = true := by decide +kernel
private theorem c580096 : checkChunk 580096 128 = true := by decide +kernel
private theorem c580224 : checkChunk 580224 128 = true := by decide +kernel
private theorem c580352 : checkChunk 580352 128 = true := by decide +kernel
private theorem c580480 : checkChunk 580480 128 = true := by decide +kernel
private theorem c580608 : checkChunk 580608 128 = true := by decide +kernel
private theorem c580736 : checkChunk 580736 128 = true := by decide +kernel
private theorem c580864 : checkChunk 580864 128 = true := by decide +kernel
private theorem c580992 : checkChunk 580992 128 = true := by decide +kernel
private theorem c581120 : checkChunk 581120 128 = true := by decide +kernel
private theorem c581248 : checkChunk 581248 128 = true := by decide +kernel
private theorem c581376 : checkChunk 581376 128 = true := by decide +kernel
private theorem c581504 : checkChunk 581504 128 = true := by decide +kernel

public theorem checked : Checked 573440 581632 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 573440 128 c573440) (checkChunk_sound 573568 128 c573568)) (Checked.append (checkChunk_sound 573696 128 c573696) (checkChunk_sound 573824 128 c573824))) (Checked.append (Checked.append (checkChunk_sound 573952 128 c573952) (checkChunk_sound 574080 128 c574080)) (Checked.append (checkChunk_sound 574208 128 c574208) (checkChunk_sound 574336 128 c574336)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 574464 128 c574464) (checkChunk_sound 574592 128 c574592)) (Checked.append (checkChunk_sound 574720 128 c574720) (checkChunk_sound 574848 128 c574848))) (Checked.append (Checked.append (checkChunk_sound 574976 128 c574976) (checkChunk_sound 575104 128 c575104)) (Checked.append (checkChunk_sound 575232 128 c575232) (checkChunk_sound 575360 128 c575360))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 575488 128 c575488) (checkChunk_sound 575616 128 c575616)) (Checked.append (checkChunk_sound 575744 128 c575744) (checkChunk_sound 575872 128 c575872))) (Checked.append (Checked.append (checkChunk_sound 576000 128 c576000) (checkChunk_sound 576128 128 c576128)) (Checked.append (checkChunk_sound 576256 128 c576256) (checkChunk_sound 576384 128 c576384)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 576512 128 c576512) (checkChunk_sound 576640 128 c576640)) (Checked.append (checkChunk_sound 576768 128 c576768) (checkChunk_sound 576896 128 c576896))) (Checked.append (Checked.append (checkChunk_sound 577024 128 c577024) (checkChunk_sound 577152 128 c577152)) (Checked.append (checkChunk_sound 577280 128 c577280) (checkChunk_sound 577408 128 c577408)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 577536 128 c577536) (checkChunk_sound 577664 128 c577664)) (Checked.append (checkChunk_sound 577792 128 c577792) (checkChunk_sound 577920 128 c577920))) (Checked.append (Checked.append (checkChunk_sound 578048 128 c578048) (checkChunk_sound 578176 128 c578176)) (Checked.append (checkChunk_sound 578304 128 c578304) (checkChunk_sound 578432 128 c578432)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 578560 128 c578560) (checkChunk_sound 578688 128 c578688)) (Checked.append (checkChunk_sound 578816 128 c578816) (checkChunk_sound 578944 128 c578944))) (Checked.append (Checked.append (checkChunk_sound 579072 128 c579072) (checkChunk_sound 579200 128 c579200)) (Checked.append (checkChunk_sound 579328 128 c579328) (checkChunk_sound 579456 128 c579456))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 579584 128 c579584) (checkChunk_sound 579712 128 c579712)) (Checked.append (checkChunk_sound 579840 128 c579840) (checkChunk_sound 579968 128 c579968))) (Checked.append (Checked.append (checkChunk_sound 580096 128 c580096) (checkChunk_sound 580224 128 c580224)) (Checked.append (checkChunk_sound 580352 128 c580352) (checkChunk_sound 580480 128 c580480)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 580608 128 c580608) (checkChunk_sound 580736 128 c580736)) (Checked.append (checkChunk_sound 580864 128 c580864) (checkChunk_sound 580992 128 c580992))) (Checked.append (Checked.append (checkChunk_sound 581120 128 c581120) (checkChunk_sound 581248 128 c581248)) (Checked.append (checkChunk_sound 581376 128 c581376) (checkChunk_sound 581504 128 c581504)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B017
