module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [155648, 163840).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B018
private theorem c155648 : checkChunk 155648 128 = true := by decide +kernel
private theorem c155776 : checkChunk 155776 128 = true := by decide +kernel
private theorem c155904 : checkChunk 155904 128 = true := by decide +kernel
private theorem c156032 : checkChunk 156032 128 = true := by decide +kernel
private theorem c156160 : checkChunk 156160 128 = true := by decide +kernel
private theorem c156288 : checkChunk 156288 128 = true := by decide +kernel
private theorem c156416 : checkChunk 156416 128 = true := by decide +kernel
private theorem c156544 : checkChunk 156544 128 = true := by decide +kernel
private theorem c156672 : checkChunk 156672 128 = true := by decide +kernel
private theorem c156800 : checkChunk 156800 128 = true := by decide +kernel
private theorem c156928 : checkChunk 156928 128 = true := by decide +kernel
private theorem c157056 : checkChunk 157056 128 = true := by decide +kernel
private theorem c157184 : checkChunk 157184 128 = true := by decide +kernel
private theorem c157312 : checkChunk 157312 128 = true := by decide +kernel
private theorem c157440 : checkChunk 157440 128 = true := by decide +kernel
private theorem c157568 : checkChunk 157568 128 = true := by decide +kernel
private theorem c157696 : checkChunk 157696 128 = true := by decide +kernel
private theorem c157824 : checkChunk 157824 128 = true := by decide +kernel
private theorem c157952 : checkChunk 157952 128 = true := by decide +kernel
private theorem c158080 : checkChunk 158080 128 = true := by decide +kernel
private theorem c158208 : checkChunk 158208 128 = true := by decide +kernel
private theorem c158336 : checkChunk 158336 128 = true := by decide +kernel
private theorem c158464 : checkChunk 158464 128 = true := by decide +kernel
private theorem c158592 : checkChunk 158592 128 = true := by decide +kernel
private theorem c158720 : checkChunk 158720 128 = true := by decide +kernel
private theorem c158848 : checkChunk 158848 128 = true := by decide +kernel
private theorem c158976 : checkChunk 158976 128 = true := by decide +kernel
private theorem c159104 : checkChunk 159104 128 = true := by decide +kernel
private theorem c159232 : checkChunk 159232 128 = true := by decide +kernel
private theorem c159360 : checkChunk 159360 128 = true := by decide +kernel
private theorem c159488 : checkChunk 159488 128 = true := by decide +kernel
private theorem c159616 : checkChunk 159616 128 = true := by decide +kernel
private theorem c159744 : checkChunk 159744 128 = true := by decide +kernel
private theorem c159872 : checkChunk 159872 128 = true := by decide +kernel
private theorem c160000 : checkChunk 160000 128 = true := by decide +kernel
private theorem c160128 : checkChunk 160128 128 = true := by decide +kernel
private theorem c160256 : checkChunk 160256 128 = true := by decide +kernel
private theorem c160384 : checkChunk 160384 128 = true := by decide +kernel
private theorem c160512 : checkChunk 160512 128 = true := by decide +kernel
private theorem c160640 : checkChunk 160640 128 = true := by decide +kernel
private theorem c160768 : checkChunk 160768 128 = true := by decide +kernel
private theorem c160896 : checkChunk 160896 128 = true := by decide +kernel
private theorem c161024 : checkChunk 161024 128 = true := by decide +kernel
private theorem c161152 : checkChunk 161152 128 = true := by decide +kernel
private theorem c161280 : checkChunk 161280 128 = true := by decide +kernel
private theorem c161408 : checkChunk 161408 128 = true := by decide +kernel
private theorem c161536 : checkChunk 161536 128 = true := by decide +kernel
private theorem c161664 : checkChunk 161664 128 = true := by decide +kernel
private theorem c161792 : checkChunk 161792 128 = true := by decide +kernel
private theorem c161920 : checkChunk 161920 128 = true := by decide +kernel
private theorem c162048 : checkChunk 162048 128 = true := by decide +kernel
private theorem c162176 : checkChunk 162176 128 = true := by decide +kernel
private theorem c162304 : checkChunk 162304 128 = true := by decide +kernel
private theorem c162432 : checkChunk 162432 128 = true := by decide +kernel
private theorem c162560 : checkChunk 162560 128 = true := by decide +kernel
private theorem c162688 : checkChunk 162688 128 = true := by decide +kernel
private theorem c162816 : checkChunk 162816 128 = true := by decide +kernel
private theorem c162944 : checkChunk 162944 128 = true := by decide +kernel
private theorem c163072 : checkChunk 163072 128 = true := by decide +kernel
private theorem c163200 : checkChunk 163200 128 = true := by decide +kernel
private theorem c163328 : checkChunk 163328 128 = true := by decide +kernel
private theorem c163456 : checkChunk 163456 128 = true := by decide +kernel
private theorem c163584 : checkChunk 163584 128 = true := by decide +kernel
private theorem c163712 : checkChunk 163712 128 = true := by decide +kernel

public theorem checked : Checked 155648 163840 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 155648 128 c155648) (checkChunk_sound 155776 128 c155776)) (Checked.append (checkChunk_sound 155904 128 c155904) (checkChunk_sound 156032 128 c156032))) (Checked.append (Checked.append (checkChunk_sound 156160 128 c156160) (checkChunk_sound 156288 128 c156288)) (Checked.append (checkChunk_sound 156416 128 c156416) (checkChunk_sound 156544 128 c156544)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 156672 128 c156672) (checkChunk_sound 156800 128 c156800)) (Checked.append (checkChunk_sound 156928 128 c156928) (checkChunk_sound 157056 128 c157056))) (Checked.append (Checked.append (checkChunk_sound 157184 128 c157184) (checkChunk_sound 157312 128 c157312)) (Checked.append (checkChunk_sound 157440 128 c157440) (checkChunk_sound 157568 128 c157568))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 157696 128 c157696) (checkChunk_sound 157824 128 c157824)) (Checked.append (checkChunk_sound 157952 128 c157952) (checkChunk_sound 158080 128 c158080))) (Checked.append (Checked.append (checkChunk_sound 158208 128 c158208) (checkChunk_sound 158336 128 c158336)) (Checked.append (checkChunk_sound 158464 128 c158464) (checkChunk_sound 158592 128 c158592)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 158720 128 c158720) (checkChunk_sound 158848 128 c158848)) (Checked.append (checkChunk_sound 158976 128 c158976) (checkChunk_sound 159104 128 c159104))) (Checked.append (Checked.append (checkChunk_sound 159232 128 c159232) (checkChunk_sound 159360 128 c159360)) (Checked.append (checkChunk_sound 159488 128 c159488) (checkChunk_sound 159616 128 c159616)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 159744 128 c159744) (checkChunk_sound 159872 128 c159872)) (Checked.append (checkChunk_sound 160000 128 c160000) (checkChunk_sound 160128 128 c160128))) (Checked.append (Checked.append (checkChunk_sound 160256 128 c160256) (checkChunk_sound 160384 128 c160384)) (Checked.append (checkChunk_sound 160512 128 c160512) (checkChunk_sound 160640 128 c160640)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 160768 128 c160768) (checkChunk_sound 160896 128 c160896)) (Checked.append (checkChunk_sound 161024 128 c161024) (checkChunk_sound 161152 128 c161152))) (Checked.append (Checked.append (checkChunk_sound 161280 128 c161280) (checkChunk_sound 161408 128 c161408)) (Checked.append (checkChunk_sound 161536 128 c161536) (checkChunk_sound 161664 128 c161664))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 161792 128 c161792) (checkChunk_sound 161920 128 c161920)) (Checked.append (checkChunk_sound 162048 128 c162048) (checkChunk_sound 162176 128 c162176))) (Checked.append (Checked.append (checkChunk_sound 162304 128 c162304) (checkChunk_sound 162432 128 c162432)) (Checked.append (checkChunk_sound 162560 128 c162560) (checkChunk_sound 162688 128 c162688)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 162816 128 c162816) (checkChunk_sound 162944 128 c162944)) (Checked.append (checkChunk_sound 163072 128 c163072) (checkChunk_sound 163200 128 c163200))) (Checked.append (Checked.append (checkChunk_sound 163328 128 c163328) (checkChunk_sound 163456 128 c163456)) (Checked.append (checkChunk_sound 163584 128 c163584) (checkChunk_sound 163712 128 c163712)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B018
