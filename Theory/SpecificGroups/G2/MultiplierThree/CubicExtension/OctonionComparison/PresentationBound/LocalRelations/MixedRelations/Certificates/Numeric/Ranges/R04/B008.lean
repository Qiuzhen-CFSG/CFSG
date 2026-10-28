module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [925696, 933888).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B008
private theorem c925696 : checkChunk 925696 128 = true := by decide +kernel
private theorem c925824 : checkChunk 925824 128 = true := by decide +kernel
private theorem c925952 : checkChunk 925952 128 = true := by decide +kernel
private theorem c926080 : checkChunk 926080 128 = true := by decide +kernel
private theorem c926208 : checkChunk 926208 128 = true := by decide +kernel
private theorem c926336 : checkChunk 926336 128 = true := by decide +kernel
private theorem c926464 : checkChunk 926464 128 = true := by decide +kernel
private theorem c926592 : checkChunk 926592 128 = true := by decide +kernel
private theorem c926720 : checkChunk 926720 128 = true := by decide +kernel
private theorem c926848 : checkChunk 926848 128 = true := by decide +kernel
private theorem c926976 : checkChunk 926976 128 = true := by decide +kernel
private theorem c927104 : checkChunk 927104 128 = true := by decide +kernel
private theorem c927232 : checkChunk 927232 128 = true := by decide +kernel
private theorem c927360 : checkChunk 927360 128 = true := by decide +kernel
private theorem c927488 : checkChunk 927488 128 = true := by decide +kernel
private theorem c927616 : checkChunk 927616 128 = true := by decide +kernel
private theorem c927744 : checkChunk 927744 128 = true := by decide +kernel
private theorem c927872 : checkChunk 927872 128 = true := by decide +kernel
private theorem c928000 : checkChunk 928000 128 = true := by decide +kernel
private theorem c928128 : checkChunk 928128 128 = true := by decide +kernel
private theorem c928256 : checkChunk 928256 128 = true := by decide +kernel
private theorem c928384 : checkChunk 928384 128 = true := by decide +kernel
private theorem c928512 : checkChunk 928512 128 = true := by decide +kernel
private theorem c928640 : checkChunk 928640 128 = true := by decide +kernel
private theorem c928768 : checkChunk 928768 128 = true := by decide +kernel
private theorem c928896 : checkChunk 928896 128 = true := by decide +kernel
private theorem c929024 : checkChunk 929024 128 = true := by decide +kernel
private theorem c929152 : checkChunk 929152 128 = true := by decide +kernel
private theorem c929280 : checkChunk 929280 128 = true := by decide +kernel
private theorem c929408 : checkChunk 929408 128 = true := by decide +kernel
private theorem c929536 : checkChunk 929536 128 = true := by decide +kernel
private theorem c929664 : checkChunk 929664 128 = true := by decide +kernel
private theorem c929792 : checkChunk 929792 128 = true := by decide +kernel
private theorem c929920 : checkChunk 929920 128 = true := by decide +kernel
private theorem c930048 : checkChunk 930048 128 = true := by decide +kernel
private theorem c930176 : checkChunk 930176 128 = true := by decide +kernel
private theorem c930304 : checkChunk 930304 128 = true := by decide +kernel
private theorem c930432 : checkChunk 930432 128 = true := by decide +kernel
private theorem c930560 : checkChunk 930560 128 = true := by decide +kernel
private theorem c930688 : checkChunk 930688 128 = true := by decide +kernel
private theorem c930816 : checkChunk 930816 128 = true := by decide +kernel
private theorem c930944 : checkChunk 930944 128 = true := by decide +kernel
private theorem c931072 : checkChunk 931072 128 = true := by decide +kernel
private theorem c931200 : checkChunk 931200 128 = true := by decide +kernel
private theorem c931328 : checkChunk 931328 128 = true := by decide +kernel
private theorem c931456 : checkChunk 931456 128 = true := by decide +kernel
private theorem c931584 : checkChunk 931584 128 = true := by decide +kernel
private theorem c931712 : checkChunk 931712 128 = true := by decide +kernel
private theorem c931840 : checkChunk 931840 128 = true := by decide +kernel
private theorem c931968 : checkChunk 931968 128 = true := by decide +kernel
private theorem c932096 : checkChunk 932096 128 = true := by decide +kernel
private theorem c932224 : checkChunk 932224 128 = true := by decide +kernel
private theorem c932352 : checkChunk 932352 128 = true := by decide +kernel
private theorem c932480 : checkChunk 932480 128 = true := by decide +kernel
private theorem c932608 : checkChunk 932608 128 = true := by decide +kernel
private theorem c932736 : checkChunk 932736 128 = true := by decide +kernel
private theorem c932864 : checkChunk 932864 128 = true := by decide +kernel
private theorem c932992 : checkChunk 932992 128 = true := by decide +kernel
private theorem c933120 : checkChunk 933120 128 = true := by decide +kernel
private theorem c933248 : checkChunk 933248 128 = true := by decide +kernel
private theorem c933376 : checkChunk 933376 128 = true := by decide +kernel
private theorem c933504 : checkChunk 933504 128 = true := by decide +kernel
private theorem c933632 : checkChunk 933632 128 = true := by decide +kernel
private theorem c933760 : checkChunk 933760 128 = true := by decide +kernel

public theorem checked : Checked 925696 933888 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 925696 128 c925696) (checkChunk_sound 925824 128 c925824)) (Checked.append (checkChunk_sound 925952 128 c925952) (checkChunk_sound 926080 128 c926080))) (Checked.append (Checked.append (checkChunk_sound 926208 128 c926208) (checkChunk_sound 926336 128 c926336)) (Checked.append (checkChunk_sound 926464 128 c926464) (checkChunk_sound 926592 128 c926592)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 926720 128 c926720) (checkChunk_sound 926848 128 c926848)) (Checked.append (checkChunk_sound 926976 128 c926976) (checkChunk_sound 927104 128 c927104))) (Checked.append (Checked.append (checkChunk_sound 927232 128 c927232) (checkChunk_sound 927360 128 c927360)) (Checked.append (checkChunk_sound 927488 128 c927488) (checkChunk_sound 927616 128 c927616))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 927744 128 c927744) (checkChunk_sound 927872 128 c927872)) (Checked.append (checkChunk_sound 928000 128 c928000) (checkChunk_sound 928128 128 c928128))) (Checked.append (Checked.append (checkChunk_sound 928256 128 c928256) (checkChunk_sound 928384 128 c928384)) (Checked.append (checkChunk_sound 928512 128 c928512) (checkChunk_sound 928640 128 c928640)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 928768 128 c928768) (checkChunk_sound 928896 128 c928896)) (Checked.append (checkChunk_sound 929024 128 c929024) (checkChunk_sound 929152 128 c929152))) (Checked.append (Checked.append (checkChunk_sound 929280 128 c929280) (checkChunk_sound 929408 128 c929408)) (Checked.append (checkChunk_sound 929536 128 c929536) (checkChunk_sound 929664 128 c929664)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 929792 128 c929792) (checkChunk_sound 929920 128 c929920)) (Checked.append (checkChunk_sound 930048 128 c930048) (checkChunk_sound 930176 128 c930176))) (Checked.append (Checked.append (checkChunk_sound 930304 128 c930304) (checkChunk_sound 930432 128 c930432)) (Checked.append (checkChunk_sound 930560 128 c930560) (checkChunk_sound 930688 128 c930688)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 930816 128 c930816) (checkChunk_sound 930944 128 c930944)) (Checked.append (checkChunk_sound 931072 128 c931072) (checkChunk_sound 931200 128 c931200))) (Checked.append (Checked.append (checkChunk_sound 931328 128 c931328) (checkChunk_sound 931456 128 c931456)) (Checked.append (checkChunk_sound 931584 128 c931584) (checkChunk_sound 931712 128 c931712))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 931840 128 c931840) (checkChunk_sound 931968 128 c931968)) (Checked.append (checkChunk_sound 932096 128 c932096) (checkChunk_sound 932224 128 c932224))) (Checked.append (Checked.append (checkChunk_sound 932352 128 c932352) (checkChunk_sound 932480 128 c932480)) (Checked.append (checkChunk_sound 932608 128 c932608) (checkChunk_sound 932736 128 c932736)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 932864 128 c932864) (checkChunk_sound 932992 128 c932992)) (Checked.append (checkChunk_sound 933120 128 c933120) (checkChunk_sound 933248 128 c933248))) (Checked.append (Checked.append (checkChunk_sound 933376 128 c933376) (checkChunk_sound 933504 128 c933504)) (Checked.append (checkChunk_sound 933632 128 c933632) (checkChunk_sound 933760 128 c933760)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B008
