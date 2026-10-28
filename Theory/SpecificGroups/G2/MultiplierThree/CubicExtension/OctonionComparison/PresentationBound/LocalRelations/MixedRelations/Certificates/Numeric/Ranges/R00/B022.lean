module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [188416, 196608).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B022
private theorem c188416 : checkChunk 188416 128 = true := by decide +kernel
private theorem c188544 : checkChunk 188544 128 = true := by decide +kernel
private theorem c188672 : checkChunk 188672 128 = true := by decide +kernel
private theorem c188800 : checkChunk 188800 128 = true := by decide +kernel
private theorem c188928 : checkChunk 188928 128 = true := by decide +kernel
private theorem c189056 : checkChunk 189056 128 = true := by decide +kernel
private theorem c189184 : checkChunk 189184 128 = true := by decide +kernel
private theorem c189312 : checkChunk 189312 128 = true := by decide +kernel
private theorem c189440 : checkChunk 189440 128 = true := by decide +kernel
private theorem c189568 : checkChunk 189568 128 = true := by decide +kernel
private theorem c189696 : checkChunk 189696 128 = true := by decide +kernel
private theorem c189824 : checkChunk 189824 128 = true := by decide +kernel
private theorem c189952 : checkChunk 189952 128 = true := by decide +kernel
private theorem c190080 : checkChunk 190080 128 = true := by decide +kernel
private theorem c190208 : checkChunk 190208 128 = true := by decide +kernel
private theorem c190336 : checkChunk 190336 128 = true := by decide +kernel
private theorem c190464 : checkChunk 190464 128 = true := by decide +kernel
private theorem c190592 : checkChunk 190592 128 = true := by decide +kernel
private theorem c190720 : checkChunk 190720 128 = true := by decide +kernel
private theorem c190848 : checkChunk 190848 128 = true := by decide +kernel
private theorem c190976 : checkChunk 190976 128 = true := by decide +kernel
private theorem c191104 : checkChunk 191104 128 = true := by decide +kernel
private theorem c191232 : checkChunk 191232 128 = true := by decide +kernel
private theorem c191360 : checkChunk 191360 128 = true := by decide +kernel
private theorem c191488 : checkChunk 191488 128 = true := by decide +kernel
private theorem c191616 : checkChunk 191616 128 = true := by decide +kernel
private theorem c191744 : checkChunk 191744 128 = true := by decide +kernel
private theorem c191872 : checkChunk 191872 128 = true := by decide +kernel
private theorem c192000 : checkChunk 192000 128 = true := by decide +kernel
private theorem c192128 : checkChunk 192128 128 = true := by decide +kernel
private theorem c192256 : checkChunk 192256 128 = true := by decide +kernel
private theorem c192384 : checkChunk 192384 128 = true := by decide +kernel
private theorem c192512 : checkChunk 192512 128 = true := by decide +kernel
private theorem c192640 : checkChunk 192640 128 = true := by decide +kernel
private theorem c192768 : checkChunk 192768 128 = true := by decide +kernel
private theorem c192896 : checkChunk 192896 128 = true := by decide +kernel
private theorem c193024 : checkChunk 193024 128 = true := by decide +kernel
private theorem c193152 : checkChunk 193152 128 = true := by decide +kernel
private theorem c193280 : checkChunk 193280 128 = true := by decide +kernel
private theorem c193408 : checkChunk 193408 128 = true := by decide +kernel
private theorem c193536 : checkChunk 193536 128 = true := by decide +kernel
private theorem c193664 : checkChunk 193664 128 = true := by decide +kernel
private theorem c193792 : checkChunk 193792 128 = true := by decide +kernel
private theorem c193920 : checkChunk 193920 128 = true := by decide +kernel
private theorem c194048 : checkChunk 194048 128 = true := by decide +kernel
private theorem c194176 : checkChunk 194176 128 = true := by decide +kernel
private theorem c194304 : checkChunk 194304 128 = true := by decide +kernel
private theorem c194432 : checkChunk 194432 128 = true := by decide +kernel
private theorem c194560 : checkChunk 194560 128 = true := by decide +kernel
private theorem c194688 : checkChunk 194688 128 = true := by decide +kernel
private theorem c194816 : checkChunk 194816 128 = true := by decide +kernel
private theorem c194944 : checkChunk 194944 128 = true := by decide +kernel
private theorem c195072 : checkChunk 195072 128 = true := by decide +kernel
private theorem c195200 : checkChunk 195200 128 = true := by decide +kernel
private theorem c195328 : checkChunk 195328 128 = true := by decide +kernel
private theorem c195456 : checkChunk 195456 128 = true := by decide +kernel
private theorem c195584 : checkChunk 195584 128 = true := by decide +kernel
private theorem c195712 : checkChunk 195712 128 = true := by decide +kernel
private theorem c195840 : checkChunk 195840 128 = true := by decide +kernel
private theorem c195968 : checkChunk 195968 128 = true := by decide +kernel
private theorem c196096 : checkChunk 196096 128 = true := by decide +kernel
private theorem c196224 : checkChunk 196224 128 = true := by decide +kernel
private theorem c196352 : checkChunk 196352 128 = true := by decide +kernel
private theorem c196480 : checkChunk 196480 128 = true := by decide +kernel

public theorem checked : Checked 188416 196608 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 188416 128 c188416) (checkChunk_sound 188544 128 c188544)) (Checked.append (checkChunk_sound 188672 128 c188672) (checkChunk_sound 188800 128 c188800))) (Checked.append (Checked.append (checkChunk_sound 188928 128 c188928) (checkChunk_sound 189056 128 c189056)) (Checked.append (checkChunk_sound 189184 128 c189184) (checkChunk_sound 189312 128 c189312)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 189440 128 c189440) (checkChunk_sound 189568 128 c189568)) (Checked.append (checkChunk_sound 189696 128 c189696) (checkChunk_sound 189824 128 c189824))) (Checked.append (Checked.append (checkChunk_sound 189952 128 c189952) (checkChunk_sound 190080 128 c190080)) (Checked.append (checkChunk_sound 190208 128 c190208) (checkChunk_sound 190336 128 c190336))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 190464 128 c190464) (checkChunk_sound 190592 128 c190592)) (Checked.append (checkChunk_sound 190720 128 c190720) (checkChunk_sound 190848 128 c190848))) (Checked.append (Checked.append (checkChunk_sound 190976 128 c190976) (checkChunk_sound 191104 128 c191104)) (Checked.append (checkChunk_sound 191232 128 c191232) (checkChunk_sound 191360 128 c191360)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 191488 128 c191488) (checkChunk_sound 191616 128 c191616)) (Checked.append (checkChunk_sound 191744 128 c191744) (checkChunk_sound 191872 128 c191872))) (Checked.append (Checked.append (checkChunk_sound 192000 128 c192000) (checkChunk_sound 192128 128 c192128)) (Checked.append (checkChunk_sound 192256 128 c192256) (checkChunk_sound 192384 128 c192384)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 192512 128 c192512) (checkChunk_sound 192640 128 c192640)) (Checked.append (checkChunk_sound 192768 128 c192768) (checkChunk_sound 192896 128 c192896))) (Checked.append (Checked.append (checkChunk_sound 193024 128 c193024) (checkChunk_sound 193152 128 c193152)) (Checked.append (checkChunk_sound 193280 128 c193280) (checkChunk_sound 193408 128 c193408)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 193536 128 c193536) (checkChunk_sound 193664 128 c193664)) (Checked.append (checkChunk_sound 193792 128 c193792) (checkChunk_sound 193920 128 c193920))) (Checked.append (Checked.append (checkChunk_sound 194048 128 c194048) (checkChunk_sound 194176 128 c194176)) (Checked.append (checkChunk_sound 194304 128 c194304) (checkChunk_sound 194432 128 c194432))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 194560 128 c194560) (checkChunk_sound 194688 128 c194688)) (Checked.append (checkChunk_sound 194816 128 c194816) (checkChunk_sound 194944 128 c194944))) (Checked.append (Checked.append (checkChunk_sound 195072 128 c195072) (checkChunk_sound 195200 128 c195200)) (Checked.append (checkChunk_sound 195328 128 c195328) (checkChunk_sound 195456 128 c195456)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 195584 128 c195584) (checkChunk_sound 195712 128 c195712)) (Checked.append (checkChunk_sound 195840 128 c195840) (checkChunk_sound 195968 128 c195968))) (Checked.append (Checked.append (checkChunk_sound 196096 128 c196096) (checkChunk_sound 196224 128 c196224)) (Checked.append (checkChunk_sound 196352 128 c196352) (checkChunk_sound 196480 128 c196480)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B022
