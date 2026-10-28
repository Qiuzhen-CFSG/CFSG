module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [565248, 573440).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B016
private theorem c565248 : checkChunk 565248 128 = true := by decide +kernel
private theorem c565376 : checkChunk 565376 128 = true := by decide +kernel
private theorem c565504 : checkChunk 565504 128 = true := by decide +kernel
private theorem c565632 : checkChunk 565632 128 = true := by decide +kernel
private theorem c565760 : checkChunk 565760 128 = true := by decide +kernel
private theorem c565888 : checkChunk 565888 128 = true := by decide +kernel
private theorem c566016 : checkChunk 566016 128 = true := by decide +kernel
private theorem c566144 : checkChunk 566144 128 = true := by decide +kernel
private theorem c566272 : checkChunk 566272 128 = true := by decide +kernel
private theorem c566400 : checkChunk 566400 128 = true := by decide +kernel
private theorem c566528 : checkChunk 566528 128 = true := by decide +kernel
private theorem c566656 : checkChunk 566656 128 = true := by decide +kernel
private theorem c566784 : checkChunk 566784 128 = true := by decide +kernel
private theorem c566912 : checkChunk 566912 128 = true := by decide +kernel
private theorem c567040 : checkChunk 567040 128 = true := by decide +kernel
private theorem c567168 : checkChunk 567168 128 = true := by decide +kernel
private theorem c567296 : checkChunk 567296 128 = true := by decide +kernel
private theorem c567424 : checkChunk 567424 128 = true := by decide +kernel
private theorem c567552 : checkChunk 567552 128 = true := by decide +kernel
private theorem c567680 : checkChunk 567680 128 = true := by decide +kernel
private theorem c567808 : checkChunk 567808 128 = true := by decide +kernel
private theorem c567936 : checkChunk 567936 128 = true := by decide +kernel
private theorem c568064 : checkChunk 568064 128 = true := by decide +kernel
private theorem c568192 : checkChunk 568192 128 = true := by decide +kernel
private theorem c568320 : checkChunk 568320 128 = true := by decide +kernel
private theorem c568448 : checkChunk 568448 128 = true := by decide +kernel
private theorem c568576 : checkChunk 568576 128 = true := by decide +kernel
private theorem c568704 : checkChunk 568704 128 = true := by decide +kernel
private theorem c568832 : checkChunk 568832 128 = true := by decide +kernel
private theorem c568960 : checkChunk 568960 128 = true := by decide +kernel
private theorem c569088 : checkChunk 569088 128 = true := by decide +kernel
private theorem c569216 : checkChunk 569216 128 = true := by decide +kernel
private theorem c569344 : checkChunk 569344 128 = true := by decide +kernel
private theorem c569472 : checkChunk 569472 128 = true := by decide +kernel
private theorem c569600 : checkChunk 569600 128 = true := by decide +kernel
private theorem c569728 : checkChunk 569728 128 = true := by decide +kernel
private theorem c569856 : checkChunk 569856 128 = true := by decide +kernel
private theorem c569984 : checkChunk 569984 128 = true := by decide +kernel
private theorem c570112 : checkChunk 570112 128 = true := by decide +kernel
private theorem c570240 : checkChunk 570240 128 = true := by decide +kernel
private theorem c570368 : checkChunk 570368 128 = true := by decide +kernel
private theorem c570496 : checkChunk 570496 128 = true := by decide +kernel
private theorem c570624 : checkChunk 570624 128 = true := by decide +kernel
private theorem c570752 : checkChunk 570752 128 = true := by decide +kernel
private theorem c570880 : checkChunk 570880 128 = true := by decide +kernel
private theorem c571008 : checkChunk 571008 128 = true := by decide +kernel
private theorem c571136 : checkChunk 571136 128 = true := by decide +kernel
private theorem c571264 : checkChunk 571264 128 = true := by decide +kernel
private theorem c571392 : checkChunk 571392 128 = true := by decide +kernel
private theorem c571520 : checkChunk 571520 128 = true := by decide +kernel
private theorem c571648 : checkChunk 571648 128 = true := by decide +kernel
private theorem c571776 : checkChunk 571776 128 = true := by decide +kernel
private theorem c571904 : checkChunk 571904 128 = true := by decide +kernel
private theorem c572032 : checkChunk 572032 128 = true := by decide +kernel
private theorem c572160 : checkChunk 572160 128 = true := by decide +kernel
private theorem c572288 : checkChunk 572288 128 = true := by decide +kernel
private theorem c572416 : checkChunk 572416 128 = true := by decide +kernel
private theorem c572544 : checkChunk 572544 128 = true := by decide +kernel
private theorem c572672 : checkChunk 572672 128 = true := by decide +kernel
private theorem c572800 : checkChunk 572800 128 = true := by decide +kernel
private theorem c572928 : checkChunk 572928 128 = true := by decide +kernel
private theorem c573056 : checkChunk 573056 128 = true := by decide +kernel
private theorem c573184 : checkChunk 573184 128 = true := by decide +kernel
private theorem c573312 : checkChunk 573312 128 = true := by decide +kernel

public theorem checked : Checked 565248 573440 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 565248 128 c565248) (checkChunk_sound 565376 128 c565376)) (Checked.append (checkChunk_sound 565504 128 c565504) (checkChunk_sound 565632 128 c565632))) (Checked.append (Checked.append (checkChunk_sound 565760 128 c565760) (checkChunk_sound 565888 128 c565888)) (Checked.append (checkChunk_sound 566016 128 c566016) (checkChunk_sound 566144 128 c566144)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 566272 128 c566272) (checkChunk_sound 566400 128 c566400)) (Checked.append (checkChunk_sound 566528 128 c566528) (checkChunk_sound 566656 128 c566656))) (Checked.append (Checked.append (checkChunk_sound 566784 128 c566784) (checkChunk_sound 566912 128 c566912)) (Checked.append (checkChunk_sound 567040 128 c567040) (checkChunk_sound 567168 128 c567168))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 567296 128 c567296) (checkChunk_sound 567424 128 c567424)) (Checked.append (checkChunk_sound 567552 128 c567552) (checkChunk_sound 567680 128 c567680))) (Checked.append (Checked.append (checkChunk_sound 567808 128 c567808) (checkChunk_sound 567936 128 c567936)) (Checked.append (checkChunk_sound 568064 128 c568064) (checkChunk_sound 568192 128 c568192)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 568320 128 c568320) (checkChunk_sound 568448 128 c568448)) (Checked.append (checkChunk_sound 568576 128 c568576) (checkChunk_sound 568704 128 c568704))) (Checked.append (Checked.append (checkChunk_sound 568832 128 c568832) (checkChunk_sound 568960 128 c568960)) (Checked.append (checkChunk_sound 569088 128 c569088) (checkChunk_sound 569216 128 c569216)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 569344 128 c569344) (checkChunk_sound 569472 128 c569472)) (Checked.append (checkChunk_sound 569600 128 c569600) (checkChunk_sound 569728 128 c569728))) (Checked.append (Checked.append (checkChunk_sound 569856 128 c569856) (checkChunk_sound 569984 128 c569984)) (Checked.append (checkChunk_sound 570112 128 c570112) (checkChunk_sound 570240 128 c570240)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 570368 128 c570368) (checkChunk_sound 570496 128 c570496)) (Checked.append (checkChunk_sound 570624 128 c570624) (checkChunk_sound 570752 128 c570752))) (Checked.append (Checked.append (checkChunk_sound 570880 128 c570880) (checkChunk_sound 571008 128 c571008)) (Checked.append (checkChunk_sound 571136 128 c571136) (checkChunk_sound 571264 128 c571264))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 571392 128 c571392) (checkChunk_sound 571520 128 c571520)) (Checked.append (checkChunk_sound 571648 128 c571648) (checkChunk_sound 571776 128 c571776))) (Checked.append (Checked.append (checkChunk_sound 571904 128 c571904) (checkChunk_sound 572032 128 c572032)) (Checked.append (checkChunk_sound 572160 128 c572160) (checkChunk_sound 572288 128 c572288)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 572416 128 c572416) (checkChunk_sound 572544 128 c572544)) (Checked.append (checkChunk_sound 572672 128 c572672) (checkChunk_sound 572800 128 c572800))) (Checked.append (Checked.append (checkChunk_sound 572928 128 c572928) (checkChunk_sound 573056 128 c573056)) (Checked.append (checkChunk_sound 573184 128 c573184) (checkChunk_sound 573312 128 c573312)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B016
