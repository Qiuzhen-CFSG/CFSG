module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [688128, 696320).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B005
private theorem c688128 : checkChunk 688128 128 = true := by decide +kernel
private theorem c688256 : checkChunk 688256 128 = true := by decide +kernel
private theorem c688384 : checkChunk 688384 128 = true := by decide +kernel
private theorem c688512 : checkChunk 688512 128 = true := by decide +kernel
private theorem c688640 : checkChunk 688640 128 = true := by decide +kernel
private theorem c688768 : checkChunk 688768 128 = true := by decide +kernel
private theorem c688896 : checkChunk 688896 128 = true := by decide +kernel
private theorem c689024 : checkChunk 689024 128 = true := by decide +kernel
private theorem c689152 : checkChunk 689152 128 = true := by decide +kernel
private theorem c689280 : checkChunk 689280 128 = true := by decide +kernel
private theorem c689408 : checkChunk 689408 128 = true := by decide +kernel
private theorem c689536 : checkChunk 689536 128 = true := by decide +kernel
private theorem c689664 : checkChunk 689664 128 = true := by decide +kernel
private theorem c689792 : checkChunk 689792 128 = true := by decide +kernel
private theorem c689920 : checkChunk 689920 128 = true := by decide +kernel
private theorem c690048 : checkChunk 690048 128 = true := by decide +kernel
private theorem c690176 : checkChunk 690176 128 = true := by decide +kernel
private theorem c690304 : checkChunk 690304 128 = true := by decide +kernel
private theorem c690432 : checkChunk 690432 128 = true := by decide +kernel
private theorem c690560 : checkChunk 690560 128 = true := by decide +kernel
private theorem c690688 : checkChunk 690688 128 = true := by decide +kernel
private theorem c690816 : checkChunk 690816 128 = true := by decide +kernel
private theorem c690944 : checkChunk 690944 128 = true := by decide +kernel
private theorem c691072 : checkChunk 691072 128 = true := by decide +kernel
private theorem c691200 : checkChunk 691200 128 = true := by decide +kernel
private theorem c691328 : checkChunk 691328 128 = true := by decide +kernel
private theorem c691456 : checkChunk 691456 128 = true := by decide +kernel
private theorem c691584 : checkChunk 691584 128 = true := by decide +kernel
private theorem c691712 : checkChunk 691712 128 = true := by decide +kernel
private theorem c691840 : checkChunk 691840 128 = true := by decide +kernel
private theorem c691968 : checkChunk 691968 128 = true := by decide +kernel
private theorem c692096 : checkChunk 692096 128 = true := by decide +kernel
private theorem c692224 : checkChunk 692224 128 = true := by decide +kernel
private theorem c692352 : checkChunk 692352 128 = true := by decide +kernel
private theorem c692480 : checkChunk 692480 128 = true := by decide +kernel
private theorem c692608 : checkChunk 692608 128 = true := by decide +kernel
private theorem c692736 : checkChunk 692736 128 = true := by decide +kernel
private theorem c692864 : checkChunk 692864 128 = true := by decide +kernel
private theorem c692992 : checkChunk 692992 128 = true := by decide +kernel
private theorem c693120 : checkChunk 693120 128 = true := by decide +kernel
private theorem c693248 : checkChunk 693248 128 = true := by decide +kernel
private theorem c693376 : checkChunk 693376 128 = true := by decide +kernel
private theorem c693504 : checkChunk 693504 128 = true := by decide +kernel
private theorem c693632 : checkChunk 693632 128 = true := by decide +kernel
private theorem c693760 : checkChunk 693760 128 = true := by decide +kernel
private theorem c693888 : checkChunk 693888 128 = true := by decide +kernel
private theorem c694016 : checkChunk 694016 128 = true := by decide +kernel
private theorem c694144 : checkChunk 694144 128 = true := by decide +kernel
private theorem c694272 : checkChunk 694272 128 = true := by decide +kernel
private theorem c694400 : checkChunk 694400 128 = true := by decide +kernel
private theorem c694528 : checkChunk 694528 128 = true := by decide +kernel
private theorem c694656 : checkChunk 694656 128 = true := by decide +kernel
private theorem c694784 : checkChunk 694784 128 = true := by decide +kernel
private theorem c694912 : checkChunk 694912 128 = true := by decide +kernel
private theorem c695040 : checkChunk 695040 128 = true := by decide +kernel
private theorem c695168 : checkChunk 695168 128 = true := by decide +kernel
private theorem c695296 : checkChunk 695296 128 = true := by decide +kernel
private theorem c695424 : checkChunk 695424 128 = true := by decide +kernel
private theorem c695552 : checkChunk 695552 128 = true := by decide +kernel
private theorem c695680 : checkChunk 695680 128 = true := by decide +kernel
private theorem c695808 : checkChunk 695808 128 = true := by decide +kernel
private theorem c695936 : checkChunk 695936 128 = true := by decide +kernel
private theorem c696064 : checkChunk 696064 128 = true := by decide +kernel
private theorem c696192 : checkChunk 696192 128 = true := by decide +kernel

public theorem checked : Checked 688128 696320 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 688128 128 c688128) (checkChunk_sound 688256 128 c688256)) (Checked.append (checkChunk_sound 688384 128 c688384) (checkChunk_sound 688512 128 c688512))) (Checked.append (Checked.append (checkChunk_sound 688640 128 c688640) (checkChunk_sound 688768 128 c688768)) (Checked.append (checkChunk_sound 688896 128 c688896) (checkChunk_sound 689024 128 c689024)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 689152 128 c689152) (checkChunk_sound 689280 128 c689280)) (Checked.append (checkChunk_sound 689408 128 c689408) (checkChunk_sound 689536 128 c689536))) (Checked.append (Checked.append (checkChunk_sound 689664 128 c689664) (checkChunk_sound 689792 128 c689792)) (Checked.append (checkChunk_sound 689920 128 c689920) (checkChunk_sound 690048 128 c690048))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 690176 128 c690176) (checkChunk_sound 690304 128 c690304)) (Checked.append (checkChunk_sound 690432 128 c690432) (checkChunk_sound 690560 128 c690560))) (Checked.append (Checked.append (checkChunk_sound 690688 128 c690688) (checkChunk_sound 690816 128 c690816)) (Checked.append (checkChunk_sound 690944 128 c690944) (checkChunk_sound 691072 128 c691072)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 691200 128 c691200) (checkChunk_sound 691328 128 c691328)) (Checked.append (checkChunk_sound 691456 128 c691456) (checkChunk_sound 691584 128 c691584))) (Checked.append (Checked.append (checkChunk_sound 691712 128 c691712) (checkChunk_sound 691840 128 c691840)) (Checked.append (checkChunk_sound 691968 128 c691968) (checkChunk_sound 692096 128 c692096)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 692224 128 c692224) (checkChunk_sound 692352 128 c692352)) (Checked.append (checkChunk_sound 692480 128 c692480) (checkChunk_sound 692608 128 c692608))) (Checked.append (Checked.append (checkChunk_sound 692736 128 c692736) (checkChunk_sound 692864 128 c692864)) (Checked.append (checkChunk_sound 692992 128 c692992) (checkChunk_sound 693120 128 c693120)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 693248 128 c693248) (checkChunk_sound 693376 128 c693376)) (Checked.append (checkChunk_sound 693504 128 c693504) (checkChunk_sound 693632 128 c693632))) (Checked.append (Checked.append (checkChunk_sound 693760 128 c693760) (checkChunk_sound 693888 128 c693888)) (Checked.append (checkChunk_sound 694016 128 c694016) (checkChunk_sound 694144 128 c694144))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 694272 128 c694272) (checkChunk_sound 694400 128 c694400)) (Checked.append (checkChunk_sound 694528 128 c694528) (checkChunk_sound 694656 128 c694656))) (Checked.append (Checked.append (checkChunk_sound 694784 128 c694784) (checkChunk_sound 694912 128 c694912)) (Checked.append (checkChunk_sound 695040 128 c695040) (checkChunk_sound 695168 128 c695168)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 695296 128 c695296) (checkChunk_sound 695424 128 c695424)) (Checked.append (checkChunk_sound 695552 128 c695552) (checkChunk_sound 695680 128 c695680))) (Checked.append (Checked.append (checkChunk_sound 695808 128 c695808) (checkChunk_sound 695936 128 c695936)) (Checked.append (checkChunk_sound 696064 128 c696064) (checkChunk_sound 696192 128 c696192)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B005
