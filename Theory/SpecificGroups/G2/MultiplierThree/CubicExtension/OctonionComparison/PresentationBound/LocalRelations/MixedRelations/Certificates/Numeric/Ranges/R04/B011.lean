module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [950272, 958464).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B011
private theorem c950272 : checkChunk 950272 128 = true := by decide +kernel
private theorem c950400 : checkChunk 950400 128 = true := by decide +kernel
private theorem c950528 : checkChunk 950528 128 = true := by decide +kernel
private theorem c950656 : checkChunk 950656 128 = true := by decide +kernel
private theorem c950784 : checkChunk 950784 128 = true := by decide +kernel
private theorem c950912 : checkChunk 950912 128 = true := by decide +kernel
private theorem c951040 : checkChunk 951040 128 = true := by decide +kernel
private theorem c951168 : checkChunk 951168 128 = true := by decide +kernel
private theorem c951296 : checkChunk 951296 128 = true := by decide +kernel
private theorem c951424 : checkChunk 951424 128 = true := by decide +kernel
private theorem c951552 : checkChunk 951552 128 = true := by decide +kernel
private theorem c951680 : checkChunk 951680 128 = true := by decide +kernel
private theorem c951808 : checkChunk 951808 128 = true := by decide +kernel
private theorem c951936 : checkChunk 951936 128 = true := by decide +kernel
private theorem c952064 : checkChunk 952064 128 = true := by decide +kernel
private theorem c952192 : checkChunk 952192 128 = true := by decide +kernel
private theorem c952320 : checkChunk 952320 128 = true := by decide +kernel
private theorem c952448 : checkChunk 952448 128 = true := by decide +kernel
private theorem c952576 : checkChunk 952576 128 = true := by decide +kernel
private theorem c952704 : checkChunk 952704 128 = true := by decide +kernel
private theorem c952832 : checkChunk 952832 128 = true := by decide +kernel
private theorem c952960 : checkChunk 952960 128 = true := by decide +kernel
private theorem c953088 : checkChunk 953088 128 = true := by decide +kernel
private theorem c953216 : checkChunk 953216 128 = true := by decide +kernel
private theorem c953344 : checkChunk 953344 128 = true := by decide +kernel
private theorem c953472 : checkChunk 953472 128 = true := by decide +kernel
private theorem c953600 : checkChunk 953600 128 = true := by decide +kernel
private theorem c953728 : checkChunk 953728 128 = true := by decide +kernel
private theorem c953856 : checkChunk 953856 128 = true := by decide +kernel
private theorem c953984 : checkChunk 953984 128 = true := by decide +kernel
private theorem c954112 : checkChunk 954112 128 = true := by decide +kernel
private theorem c954240 : checkChunk 954240 128 = true := by decide +kernel
private theorem c954368 : checkChunk 954368 128 = true := by decide +kernel
private theorem c954496 : checkChunk 954496 128 = true := by decide +kernel
private theorem c954624 : checkChunk 954624 128 = true := by decide +kernel
private theorem c954752 : checkChunk 954752 128 = true := by decide +kernel
private theorem c954880 : checkChunk 954880 128 = true := by decide +kernel
private theorem c955008 : checkChunk 955008 128 = true := by decide +kernel
private theorem c955136 : checkChunk 955136 128 = true := by decide +kernel
private theorem c955264 : checkChunk 955264 128 = true := by decide +kernel
private theorem c955392 : checkChunk 955392 128 = true := by decide +kernel
private theorem c955520 : checkChunk 955520 128 = true := by decide +kernel
private theorem c955648 : checkChunk 955648 128 = true := by decide +kernel
private theorem c955776 : checkChunk 955776 128 = true := by decide +kernel
private theorem c955904 : checkChunk 955904 128 = true := by decide +kernel
private theorem c956032 : checkChunk 956032 128 = true := by decide +kernel
private theorem c956160 : checkChunk 956160 128 = true := by decide +kernel
private theorem c956288 : checkChunk 956288 128 = true := by decide +kernel
private theorem c956416 : checkChunk 956416 128 = true := by decide +kernel
private theorem c956544 : checkChunk 956544 128 = true := by decide +kernel
private theorem c956672 : checkChunk 956672 128 = true := by decide +kernel
private theorem c956800 : checkChunk 956800 128 = true := by decide +kernel
private theorem c956928 : checkChunk 956928 128 = true := by decide +kernel
private theorem c957056 : checkChunk 957056 128 = true := by decide +kernel
private theorem c957184 : checkChunk 957184 128 = true := by decide +kernel
private theorem c957312 : checkChunk 957312 128 = true := by decide +kernel
private theorem c957440 : checkChunk 957440 128 = true := by decide +kernel
private theorem c957568 : checkChunk 957568 128 = true := by decide +kernel
private theorem c957696 : checkChunk 957696 128 = true := by decide +kernel
private theorem c957824 : checkChunk 957824 128 = true := by decide +kernel
private theorem c957952 : checkChunk 957952 128 = true := by decide +kernel
private theorem c958080 : checkChunk 958080 128 = true := by decide +kernel
private theorem c958208 : checkChunk 958208 128 = true := by decide +kernel
private theorem c958336 : checkChunk 958336 128 = true := by decide +kernel

public theorem checked : Checked 950272 958464 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 950272 128 c950272) (checkChunk_sound 950400 128 c950400)) (Checked.append (checkChunk_sound 950528 128 c950528) (checkChunk_sound 950656 128 c950656))) (Checked.append (Checked.append (checkChunk_sound 950784 128 c950784) (checkChunk_sound 950912 128 c950912)) (Checked.append (checkChunk_sound 951040 128 c951040) (checkChunk_sound 951168 128 c951168)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 951296 128 c951296) (checkChunk_sound 951424 128 c951424)) (Checked.append (checkChunk_sound 951552 128 c951552) (checkChunk_sound 951680 128 c951680))) (Checked.append (Checked.append (checkChunk_sound 951808 128 c951808) (checkChunk_sound 951936 128 c951936)) (Checked.append (checkChunk_sound 952064 128 c952064) (checkChunk_sound 952192 128 c952192))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 952320 128 c952320) (checkChunk_sound 952448 128 c952448)) (Checked.append (checkChunk_sound 952576 128 c952576) (checkChunk_sound 952704 128 c952704))) (Checked.append (Checked.append (checkChunk_sound 952832 128 c952832) (checkChunk_sound 952960 128 c952960)) (Checked.append (checkChunk_sound 953088 128 c953088) (checkChunk_sound 953216 128 c953216)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 953344 128 c953344) (checkChunk_sound 953472 128 c953472)) (Checked.append (checkChunk_sound 953600 128 c953600) (checkChunk_sound 953728 128 c953728))) (Checked.append (Checked.append (checkChunk_sound 953856 128 c953856) (checkChunk_sound 953984 128 c953984)) (Checked.append (checkChunk_sound 954112 128 c954112) (checkChunk_sound 954240 128 c954240)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 954368 128 c954368) (checkChunk_sound 954496 128 c954496)) (Checked.append (checkChunk_sound 954624 128 c954624) (checkChunk_sound 954752 128 c954752))) (Checked.append (Checked.append (checkChunk_sound 954880 128 c954880) (checkChunk_sound 955008 128 c955008)) (Checked.append (checkChunk_sound 955136 128 c955136) (checkChunk_sound 955264 128 c955264)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 955392 128 c955392) (checkChunk_sound 955520 128 c955520)) (Checked.append (checkChunk_sound 955648 128 c955648) (checkChunk_sound 955776 128 c955776))) (Checked.append (Checked.append (checkChunk_sound 955904 128 c955904) (checkChunk_sound 956032 128 c956032)) (Checked.append (checkChunk_sound 956160 128 c956160) (checkChunk_sound 956288 128 c956288))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 956416 128 c956416) (checkChunk_sound 956544 128 c956544)) (Checked.append (checkChunk_sound 956672 128 c956672) (checkChunk_sound 956800 128 c956800))) (Checked.append (Checked.append (checkChunk_sound 956928 128 c956928) (checkChunk_sound 957056 128 c957056)) (Checked.append (checkChunk_sound 957184 128 c957184) (checkChunk_sound 957312 128 c957312)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 957440 128 c957440) (checkChunk_sound 957568 128 c957568)) (Checked.append (checkChunk_sound 957696 128 c957696) (checkChunk_sound 957824 128 c957824))) (Checked.append (Checked.append (checkChunk_sound 957952 128 c957952) (checkChunk_sound 958080 128 c958080)) (Checked.append (checkChunk_sound 958208 128 c958208) (checkChunk_sound 958336 128 c958336)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B011
