module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [991232, 999424).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B016
private theorem c991232 : checkChunk 991232 128 = true := by decide +kernel
private theorem c991360 : checkChunk 991360 128 = true := by decide +kernel
private theorem c991488 : checkChunk 991488 128 = true := by decide +kernel
private theorem c991616 : checkChunk 991616 128 = true := by decide +kernel
private theorem c991744 : checkChunk 991744 128 = true := by decide +kernel
private theorem c991872 : checkChunk 991872 128 = true := by decide +kernel
private theorem c992000 : checkChunk 992000 128 = true := by decide +kernel
private theorem c992128 : checkChunk 992128 128 = true := by decide +kernel
private theorem c992256 : checkChunk 992256 128 = true := by decide +kernel
private theorem c992384 : checkChunk 992384 128 = true := by decide +kernel
private theorem c992512 : checkChunk 992512 128 = true := by decide +kernel
private theorem c992640 : checkChunk 992640 128 = true := by decide +kernel
private theorem c992768 : checkChunk 992768 128 = true := by decide +kernel
private theorem c992896 : checkChunk 992896 128 = true := by decide +kernel
private theorem c993024 : checkChunk 993024 128 = true := by decide +kernel
private theorem c993152 : checkChunk 993152 128 = true := by decide +kernel
private theorem c993280 : checkChunk 993280 128 = true := by decide +kernel
private theorem c993408 : checkChunk 993408 128 = true := by decide +kernel
private theorem c993536 : checkChunk 993536 128 = true := by decide +kernel
private theorem c993664 : checkChunk 993664 128 = true := by decide +kernel
private theorem c993792 : checkChunk 993792 128 = true := by decide +kernel
private theorem c993920 : checkChunk 993920 128 = true := by decide +kernel
private theorem c994048 : checkChunk 994048 128 = true := by decide +kernel
private theorem c994176 : checkChunk 994176 128 = true := by decide +kernel
private theorem c994304 : checkChunk 994304 128 = true := by decide +kernel
private theorem c994432 : checkChunk 994432 128 = true := by decide +kernel
private theorem c994560 : checkChunk 994560 128 = true := by decide +kernel
private theorem c994688 : checkChunk 994688 128 = true := by decide +kernel
private theorem c994816 : checkChunk 994816 128 = true := by decide +kernel
private theorem c994944 : checkChunk 994944 128 = true := by decide +kernel
private theorem c995072 : checkChunk 995072 128 = true := by decide +kernel
private theorem c995200 : checkChunk 995200 128 = true := by decide +kernel
private theorem c995328 : checkChunk 995328 128 = true := by decide +kernel
private theorem c995456 : checkChunk 995456 128 = true := by decide +kernel
private theorem c995584 : checkChunk 995584 128 = true := by decide +kernel
private theorem c995712 : checkChunk 995712 128 = true := by decide +kernel
private theorem c995840 : checkChunk 995840 128 = true := by decide +kernel
private theorem c995968 : checkChunk 995968 128 = true := by decide +kernel
private theorem c996096 : checkChunk 996096 128 = true := by decide +kernel
private theorem c996224 : checkChunk 996224 128 = true := by decide +kernel
private theorem c996352 : checkChunk 996352 128 = true := by decide +kernel
private theorem c996480 : checkChunk 996480 128 = true := by decide +kernel
private theorem c996608 : checkChunk 996608 128 = true := by decide +kernel
private theorem c996736 : checkChunk 996736 128 = true := by decide +kernel
private theorem c996864 : checkChunk 996864 128 = true := by decide +kernel
private theorem c996992 : checkChunk 996992 128 = true := by decide +kernel
private theorem c997120 : checkChunk 997120 128 = true := by decide +kernel
private theorem c997248 : checkChunk 997248 128 = true := by decide +kernel
private theorem c997376 : checkChunk 997376 128 = true := by decide +kernel
private theorem c997504 : checkChunk 997504 128 = true := by decide +kernel
private theorem c997632 : checkChunk 997632 128 = true := by decide +kernel
private theorem c997760 : checkChunk 997760 128 = true := by decide +kernel
private theorem c997888 : checkChunk 997888 128 = true := by decide +kernel
private theorem c998016 : checkChunk 998016 128 = true := by decide +kernel
private theorem c998144 : checkChunk 998144 128 = true := by decide +kernel
private theorem c998272 : checkChunk 998272 128 = true := by decide +kernel
private theorem c998400 : checkChunk 998400 128 = true := by decide +kernel
private theorem c998528 : checkChunk 998528 128 = true := by decide +kernel
private theorem c998656 : checkChunk 998656 128 = true := by decide +kernel
private theorem c998784 : checkChunk 998784 128 = true := by decide +kernel
private theorem c998912 : checkChunk 998912 128 = true := by decide +kernel
private theorem c999040 : checkChunk 999040 128 = true := by decide +kernel
private theorem c999168 : checkChunk 999168 128 = true := by decide +kernel
private theorem c999296 : checkChunk 999296 128 = true := by decide +kernel

public theorem checked : Checked 991232 999424 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 991232 128 c991232) (checkChunk_sound 991360 128 c991360)) (Checked.append (checkChunk_sound 991488 128 c991488) (checkChunk_sound 991616 128 c991616))) (Checked.append (Checked.append (checkChunk_sound 991744 128 c991744) (checkChunk_sound 991872 128 c991872)) (Checked.append (checkChunk_sound 992000 128 c992000) (checkChunk_sound 992128 128 c992128)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 992256 128 c992256) (checkChunk_sound 992384 128 c992384)) (Checked.append (checkChunk_sound 992512 128 c992512) (checkChunk_sound 992640 128 c992640))) (Checked.append (Checked.append (checkChunk_sound 992768 128 c992768) (checkChunk_sound 992896 128 c992896)) (Checked.append (checkChunk_sound 993024 128 c993024) (checkChunk_sound 993152 128 c993152))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 993280 128 c993280) (checkChunk_sound 993408 128 c993408)) (Checked.append (checkChunk_sound 993536 128 c993536) (checkChunk_sound 993664 128 c993664))) (Checked.append (Checked.append (checkChunk_sound 993792 128 c993792) (checkChunk_sound 993920 128 c993920)) (Checked.append (checkChunk_sound 994048 128 c994048) (checkChunk_sound 994176 128 c994176)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 994304 128 c994304) (checkChunk_sound 994432 128 c994432)) (Checked.append (checkChunk_sound 994560 128 c994560) (checkChunk_sound 994688 128 c994688))) (Checked.append (Checked.append (checkChunk_sound 994816 128 c994816) (checkChunk_sound 994944 128 c994944)) (Checked.append (checkChunk_sound 995072 128 c995072) (checkChunk_sound 995200 128 c995200)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 995328 128 c995328) (checkChunk_sound 995456 128 c995456)) (Checked.append (checkChunk_sound 995584 128 c995584) (checkChunk_sound 995712 128 c995712))) (Checked.append (Checked.append (checkChunk_sound 995840 128 c995840) (checkChunk_sound 995968 128 c995968)) (Checked.append (checkChunk_sound 996096 128 c996096) (checkChunk_sound 996224 128 c996224)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 996352 128 c996352) (checkChunk_sound 996480 128 c996480)) (Checked.append (checkChunk_sound 996608 128 c996608) (checkChunk_sound 996736 128 c996736))) (Checked.append (Checked.append (checkChunk_sound 996864 128 c996864) (checkChunk_sound 996992 128 c996992)) (Checked.append (checkChunk_sound 997120 128 c997120) (checkChunk_sound 997248 128 c997248))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 997376 128 c997376) (checkChunk_sound 997504 128 c997504)) (Checked.append (checkChunk_sound 997632 128 c997632) (checkChunk_sound 997760 128 c997760))) (Checked.append (Checked.append (checkChunk_sound 997888 128 c997888) (checkChunk_sound 998016 128 c998016)) (Checked.append (checkChunk_sound 998144 128 c998144) (checkChunk_sound 998272 128 c998272)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 998400 128 c998400) (checkChunk_sound 998528 128 c998528)) (Checked.append (checkChunk_sound 998656 128 c998656) (checkChunk_sound 998784 128 c998784))) (Checked.append (Checked.append (checkChunk_sound 998912 128 c998912) (checkChunk_sound 999040 128 c999040)) (Checked.append (checkChunk_sound 999168 128 c999168) (checkChunk_sound 999296 128 c999296)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B016
