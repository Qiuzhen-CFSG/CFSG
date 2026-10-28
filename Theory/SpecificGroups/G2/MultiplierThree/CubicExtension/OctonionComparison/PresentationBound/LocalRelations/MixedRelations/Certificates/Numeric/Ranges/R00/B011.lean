module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [98304, 106496).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B011
private theorem c98304 : checkChunk 98304 128 = true := by decide +kernel
private theorem c98432 : checkChunk 98432 128 = true := by decide +kernel
private theorem c98560 : checkChunk 98560 128 = true := by decide +kernel
private theorem c98688 : checkChunk 98688 128 = true := by decide +kernel
private theorem c98816 : checkChunk 98816 128 = true := by decide +kernel
private theorem c98944 : checkChunk 98944 128 = true := by decide +kernel
private theorem c99072 : checkChunk 99072 128 = true := by decide +kernel
private theorem c99200 : checkChunk 99200 128 = true := by decide +kernel
private theorem c99328 : checkChunk 99328 128 = true := by decide +kernel
private theorem c99456 : checkChunk 99456 128 = true := by decide +kernel
private theorem c99584 : checkChunk 99584 128 = true := by decide +kernel
private theorem c99712 : checkChunk 99712 128 = true := by decide +kernel
private theorem c99840 : checkChunk 99840 128 = true := by decide +kernel
private theorem c99968 : checkChunk 99968 128 = true := by decide +kernel
private theorem c100096 : checkChunk 100096 128 = true := by decide +kernel
private theorem c100224 : checkChunk 100224 128 = true := by decide +kernel
private theorem c100352 : checkChunk 100352 128 = true := by decide +kernel
private theorem c100480 : checkChunk 100480 128 = true := by decide +kernel
private theorem c100608 : checkChunk 100608 128 = true := by decide +kernel
private theorem c100736 : checkChunk 100736 128 = true := by decide +kernel
private theorem c100864 : checkChunk 100864 128 = true := by decide +kernel
private theorem c100992 : checkChunk 100992 128 = true := by decide +kernel
private theorem c101120 : checkChunk 101120 128 = true := by decide +kernel
private theorem c101248 : checkChunk 101248 128 = true := by decide +kernel
private theorem c101376 : checkChunk 101376 128 = true := by decide +kernel
private theorem c101504 : checkChunk 101504 128 = true := by decide +kernel
private theorem c101632 : checkChunk 101632 128 = true := by decide +kernel
private theorem c101760 : checkChunk 101760 128 = true := by decide +kernel
private theorem c101888 : checkChunk 101888 128 = true := by decide +kernel
private theorem c102016 : checkChunk 102016 128 = true := by decide +kernel
private theorem c102144 : checkChunk 102144 128 = true := by decide +kernel
private theorem c102272 : checkChunk 102272 128 = true := by decide +kernel
private theorem c102400 : checkChunk 102400 128 = true := by decide +kernel
private theorem c102528 : checkChunk 102528 128 = true := by decide +kernel
private theorem c102656 : checkChunk 102656 128 = true := by decide +kernel
private theorem c102784 : checkChunk 102784 128 = true := by decide +kernel
private theorem c102912 : checkChunk 102912 128 = true := by decide +kernel
private theorem c103040 : checkChunk 103040 128 = true := by decide +kernel
private theorem c103168 : checkChunk 103168 128 = true := by decide +kernel
private theorem c103296 : checkChunk 103296 128 = true := by decide +kernel
private theorem c103424 : checkChunk 103424 128 = true := by decide +kernel
private theorem c103552 : checkChunk 103552 128 = true := by decide +kernel
private theorem c103680 : checkChunk 103680 128 = true := by decide +kernel
private theorem c103808 : checkChunk 103808 128 = true := by decide +kernel
private theorem c103936 : checkChunk 103936 128 = true := by decide +kernel
private theorem c104064 : checkChunk 104064 128 = true := by decide +kernel
private theorem c104192 : checkChunk 104192 128 = true := by decide +kernel
private theorem c104320 : checkChunk 104320 128 = true := by decide +kernel
private theorem c104448 : checkChunk 104448 128 = true := by decide +kernel
private theorem c104576 : checkChunk 104576 128 = true := by decide +kernel
private theorem c104704 : checkChunk 104704 128 = true := by decide +kernel
private theorem c104832 : checkChunk 104832 128 = true := by decide +kernel
private theorem c104960 : checkChunk 104960 128 = true := by decide +kernel
private theorem c105088 : checkChunk 105088 128 = true := by decide +kernel
private theorem c105216 : checkChunk 105216 128 = true := by decide +kernel
private theorem c105344 : checkChunk 105344 128 = true := by decide +kernel
private theorem c105472 : checkChunk 105472 128 = true := by decide +kernel
private theorem c105600 : checkChunk 105600 128 = true := by decide +kernel
private theorem c105728 : checkChunk 105728 128 = true := by decide +kernel
private theorem c105856 : checkChunk 105856 128 = true := by decide +kernel
private theorem c105984 : checkChunk 105984 128 = true := by decide +kernel
private theorem c106112 : checkChunk 106112 128 = true := by decide +kernel
private theorem c106240 : checkChunk 106240 128 = true := by decide +kernel
private theorem c106368 : checkChunk 106368 128 = true := by decide +kernel

public theorem checked : Checked 98304 106496 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 98304 128 c98304) (checkChunk_sound 98432 128 c98432)) (Checked.append (checkChunk_sound 98560 128 c98560) (checkChunk_sound 98688 128 c98688))) (Checked.append (Checked.append (checkChunk_sound 98816 128 c98816) (checkChunk_sound 98944 128 c98944)) (Checked.append (checkChunk_sound 99072 128 c99072) (checkChunk_sound 99200 128 c99200)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 99328 128 c99328) (checkChunk_sound 99456 128 c99456)) (Checked.append (checkChunk_sound 99584 128 c99584) (checkChunk_sound 99712 128 c99712))) (Checked.append (Checked.append (checkChunk_sound 99840 128 c99840) (checkChunk_sound 99968 128 c99968)) (Checked.append (checkChunk_sound 100096 128 c100096) (checkChunk_sound 100224 128 c100224))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 100352 128 c100352) (checkChunk_sound 100480 128 c100480)) (Checked.append (checkChunk_sound 100608 128 c100608) (checkChunk_sound 100736 128 c100736))) (Checked.append (Checked.append (checkChunk_sound 100864 128 c100864) (checkChunk_sound 100992 128 c100992)) (Checked.append (checkChunk_sound 101120 128 c101120) (checkChunk_sound 101248 128 c101248)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 101376 128 c101376) (checkChunk_sound 101504 128 c101504)) (Checked.append (checkChunk_sound 101632 128 c101632) (checkChunk_sound 101760 128 c101760))) (Checked.append (Checked.append (checkChunk_sound 101888 128 c101888) (checkChunk_sound 102016 128 c102016)) (Checked.append (checkChunk_sound 102144 128 c102144) (checkChunk_sound 102272 128 c102272)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 102400 128 c102400) (checkChunk_sound 102528 128 c102528)) (Checked.append (checkChunk_sound 102656 128 c102656) (checkChunk_sound 102784 128 c102784))) (Checked.append (Checked.append (checkChunk_sound 102912 128 c102912) (checkChunk_sound 103040 128 c103040)) (Checked.append (checkChunk_sound 103168 128 c103168) (checkChunk_sound 103296 128 c103296)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 103424 128 c103424) (checkChunk_sound 103552 128 c103552)) (Checked.append (checkChunk_sound 103680 128 c103680) (checkChunk_sound 103808 128 c103808))) (Checked.append (Checked.append (checkChunk_sound 103936 128 c103936) (checkChunk_sound 104064 128 c104064)) (Checked.append (checkChunk_sound 104192 128 c104192) (checkChunk_sound 104320 128 c104320))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 104448 128 c104448) (checkChunk_sound 104576 128 c104576)) (Checked.append (checkChunk_sound 104704 128 c104704) (checkChunk_sound 104832 128 c104832))) (Checked.append (Checked.append (checkChunk_sound 104960 128 c104960) (checkChunk_sound 105088 128 c105088)) (Checked.append (checkChunk_sound 105216 128 c105216) (checkChunk_sound 105344 128 c105344)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 105472 128 c105472) (checkChunk_sound 105600 128 c105600)) (Checked.append (checkChunk_sound 105728 128 c105728) (checkChunk_sound 105856 128 c105856))) (Checked.append (Checked.append (checkChunk_sound 105984 128 c105984) (checkChunk_sound 106112 128 c106112)) (Checked.append (checkChunk_sound 106240 128 c106240) (checkChunk_sound 106368 128 c106368)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B011
