module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [212992, 221184).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B025
private theorem c212992 : checkChunk 212992 128 = true := by decide +kernel
private theorem c213120 : checkChunk 213120 128 = true := by decide +kernel
private theorem c213248 : checkChunk 213248 128 = true := by decide +kernel
private theorem c213376 : checkChunk 213376 128 = true := by decide +kernel
private theorem c213504 : checkChunk 213504 128 = true := by decide +kernel
private theorem c213632 : checkChunk 213632 128 = true := by decide +kernel
private theorem c213760 : checkChunk 213760 128 = true := by decide +kernel
private theorem c213888 : checkChunk 213888 128 = true := by decide +kernel
private theorem c214016 : checkChunk 214016 128 = true := by decide +kernel
private theorem c214144 : checkChunk 214144 128 = true := by decide +kernel
private theorem c214272 : checkChunk 214272 128 = true := by decide +kernel
private theorem c214400 : checkChunk 214400 128 = true := by decide +kernel
private theorem c214528 : checkChunk 214528 128 = true := by decide +kernel
private theorem c214656 : checkChunk 214656 128 = true := by decide +kernel
private theorem c214784 : checkChunk 214784 128 = true := by decide +kernel
private theorem c214912 : checkChunk 214912 128 = true := by decide +kernel
private theorem c215040 : checkChunk 215040 128 = true := by decide +kernel
private theorem c215168 : checkChunk 215168 128 = true := by decide +kernel
private theorem c215296 : checkChunk 215296 128 = true := by decide +kernel
private theorem c215424 : checkChunk 215424 128 = true := by decide +kernel
private theorem c215552 : checkChunk 215552 128 = true := by decide +kernel
private theorem c215680 : checkChunk 215680 128 = true := by decide +kernel
private theorem c215808 : checkChunk 215808 128 = true := by decide +kernel
private theorem c215936 : checkChunk 215936 128 = true := by decide +kernel
private theorem c216064 : checkChunk 216064 128 = true := by decide +kernel
private theorem c216192 : checkChunk 216192 128 = true := by decide +kernel
private theorem c216320 : checkChunk 216320 128 = true := by decide +kernel
private theorem c216448 : checkChunk 216448 128 = true := by decide +kernel
private theorem c216576 : checkChunk 216576 128 = true := by decide +kernel
private theorem c216704 : checkChunk 216704 128 = true := by decide +kernel
private theorem c216832 : checkChunk 216832 128 = true := by decide +kernel
private theorem c216960 : checkChunk 216960 128 = true := by decide +kernel
private theorem c217088 : checkChunk 217088 128 = true := by decide +kernel
private theorem c217216 : checkChunk 217216 128 = true := by decide +kernel
private theorem c217344 : checkChunk 217344 128 = true := by decide +kernel
private theorem c217472 : checkChunk 217472 128 = true := by decide +kernel
private theorem c217600 : checkChunk 217600 128 = true := by decide +kernel
private theorem c217728 : checkChunk 217728 128 = true := by decide +kernel
private theorem c217856 : checkChunk 217856 128 = true := by decide +kernel
private theorem c217984 : checkChunk 217984 128 = true := by decide +kernel
private theorem c218112 : checkChunk 218112 128 = true := by decide +kernel
private theorem c218240 : checkChunk 218240 128 = true := by decide +kernel
private theorem c218368 : checkChunk 218368 128 = true := by decide +kernel
private theorem c218496 : checkChunk 218496 128 = true := by decide +kernel
private theorem c218624 : checkChunk 218624 128 = true := by decide +kernel
private theorem c218752 : checkChunk 218752 128 = true := by decide +kernel
private theorem c218880 : checkChunk 218880 128 = true := by decide +kernel
private theorem c219008 : checkChunk 219008 128 = true := by decide +kernel
private theorem c219136 : checkChunk 219136 128 = true := by decide +kernel
private theorem c219264 : checkChunk 219264 128 = true := by decide +kernel
private theorem c219392 : checkChunk 219392 128 = true := by decide +kernel
private theorem c219520 : checkChunk 219520 128 = true := by decide +kernel
private theorem c219648 : checkChunk 219648 128 = true := by decide +kernel
private theorem c219776 : checkChunk 219776 128 = true := by decide +kernel
private theorem c219904 : checkChunk 219904 128 = true := by decide +kernel
private theorem c220032 : checkChunk 220032 128 = true := by decide +kernel
private theorem c220160 : checkChunk 220160 128 = true := by decide +kernel
private theorem c220288 : checkChunk 220288 128 = true := by decide +kernel
private theorem c220416 : checkChunk 220416 128 = true := by decide +kernel
private theorem c220544 : checkChunk 220544 128 = true := by decide +kernel
private theorem c220672 : checkChunk 220672 128 = true := by decide +kernel
private theorem c220800 : checkChunk 220800 128 = true := by decide +kernel
private theorem c220928 : checkChunk 220928 128 = true := by decide +kernel
private theorem c221056 : checkChunk 221056 128 = true := by decide +kernel

public theorem checked : Checked 212992 221184 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 212992 128 c212992) (checkChunk_sound 213120 128 c213120)) (Checked.append (checkChunk_sound 213248 128 c213248) (checkChunk_sound 213376 128 c213376))) (Checked.append (Checked.append (checkChunk_sound 213504 128 c213504) (checkChunk_sound 213632 128 c213632)) (Checked.append (checkChunk_sound 213760 128 c213760) (checkChunk_sound 213888 128 c213888)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 214016 128 c214016) (checkChunk_sound 214144 128 c214144)) (Checked.append (checkChunk_sound 214272 128 c214272) (checkChunk_sound 214400 128 c214400))) (Checked.append (Checked.append (checkChunk_sound 214528 128 c214528) (checkChunk_sound 214656 128 c214656)) (Checked.append (checkChunk_sound 214784 128 c214784) (checkChunk_sound 214912 128 c214912))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 215040 128 c215040) (checkChunk_sound 215168 128 c215168)) (Checked.append (checkChunk_sound 215296 128 c215296) (checkChunk_sound 215424 128 c215424))) (Checked.append (Checked.append (checkChunk_sound 215552 128 c215552) (checkChunk_sound 215680 128 c215680)) (Checked.append (checkChunk_sound 215808 128 c215808) (checkChunk_sound 215936 128 c215936)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 216064 128 c216064) (checkChunk_sound 216192 128 c216192)) (Checked.append (checkChunk_sound 216320 128 c216320) (checkChunk_sound 216448 128 c216448))) (Checked.append (Checked.append (checkChunk_sound 216576 128 c216576) (checkChunk_sound 216704 128 c216704)) (Checked.append (checkChunk_sound 216832 128 c216832) (checkChunk_sound 216960 128 c216960)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 217088 128 c217088) (checkChunk_sound 217216 128 c217216)) (Checked.append (checkChunk_sound 217344 128 c217344) (checkChunk_sound 217472 128 c217472))) (Checked.append (Checked.append (checkChunk_sound 217600 128 c217600) (checkChunk_sound 217728 128 c217728)) (Checked.append (checkChunk_sound 217856 128 c217856) (checkChunk_sound 217984 128 c217984)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 218112 128 c218112) (checkChunk_sound 218240 128 c218240)) (Checked.append (checkChunk_sound 218368 128 c218368) (checkChunk_sound 218496 128 c218496))) (Checked.append (Checked.append (checkChunk_sound 218624 128 c218624) (checkChunk_sound 218752 128 c218752)) (Checked.append (checkChunk_sound 218880 128 c218880) (checkChunk_sound 219008 128 c219008))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 219136 128 c219136) (checkChunk_sound 219264 128 c219264)) (Checked.append (checkChunk_sound 219392 128 c219392) (checkChunk_sound 219520 128 c219520))) (Checked.append (Checked.append (checkChunk_sound 219648 128 c219648) (checkChunk_sound 219776 128 c219776)) (Checked.append (checkChunk_sound 219904 128 c219904) (checkChunk_sound 220032 128 c220032)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 220160 128 c220160) (checkChunk_sound 220288 128 c220288)) (Checked.append (checkChunk_sound 220416 128 c220416) (checkChunk_sound 220544 128 c220544))) (Checked.append (Checked.append (checkChunk_sound 220672 128 c220672) (checkChunk_sound 220800 128 c220800)) (Checked.append (checkChunk_sound 220928 128 c220928) (checkChunk_sound 221056 128 c221056)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B025
