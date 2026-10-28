module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [376832, 385024).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B019
private theorem c376832 : checkChunk 376832 128 = true := by decide +kernel
private theorem c376960 : checkChunk 376960 128 = true := by decide +kernel
private theorem c377088 : checkChunk 377088 128 = true := by decide +kernel
private theorem c377216 : checkChunk 377216 128 = true := by decide +kernel
private theorem c377344 : checkChunk 377344 128 = true := by decide +kernel
private theorem c377472 : checkChunk 377472 128 = true := by decide +kernel
private theorem c377600 : checkChunk 377600 128 = true := by decide +kernel
private theorem c377728 : checkChunk 377728 128 = true := by decide +kernel
private theorem c377856 : checkChunk 377856 128 = true := by decide +kernel
private theorem c377984 : checkChunk 377984 128 = true := by decide +kernel
private theorem c378112 : checkChunk 378112 128 = true := by decide +kernel
private theorem c378240 : checkChunk 378240 128 = true := by decide +kernel
private theorem c378368 : checkChunk 378368 128 = true := by decide +kernel
private theorem c378496 : checkChunk 378496 128 = true := by decide +kernel
private theorem c378624 : checkChunk 378624 128 = true := by decide +kernel
private theorem c378752 : checkChunk 378752 128 = true := by decide +kernel
private theorem c378880 : checkChunk 378880 128 = true := by decide +kernel
private theorem c379008 : checkChunk 379008 128 = true := by decide +kernel
private theorem c379136 : checkChunk 379136 128 = true := by decide +kernel
private theorem c379264 : checkChunk 379264 128 = true := by decide +kernel
private theorem c379392 : checkChunk 379392 128 = true := by decide +kernel
private theorem c379520 : checkChunk 379520 128 = true := by decide +kernel
private theorem c379648 : checkChunk 379648 128 = true := by decide +kernel
private theorem c379776 : checkChunk 379776 128 = true := by decide +kernel
private theorem c379904 : checkChunk 379904 128 = true := by decide +kernel
private theorem c380032 : checkChunk 380032 128 = true := by decide +kernel
private theorem c380160 : checkChunk 380160 128 = true := by decide +kernel
private theorem c380288 : checkChunk 380288 128 = true := by decide +kernel
private theorem c380416 : checkChunk 380416 128 = true := by decide +kernel
private theorem c380544 : checkChunk 380544 128 = true := by decide +kernel
private theorem c380672 : checkChunk 380672 128 = true := by decide +kernel
private theorem c380800 : checkChunk 380800 128 = true := by decide +kernel
private theorem c380928 : checkChunk 380928 128 = true := by decide +kernel
private theorem c381056 : checkChunk 381056 128 = true := by decide +kernel
private theorem c381184 : checkChunk 381184 128 = true := by decide +kernel
private theorem c381312 : checkChunk 381312 128 = true := by decide +kernel
private theorem c381440 : checkChunk 381440 128 = true := by decide +kernel
private theorem c381568 : checkChunk 381568 128 = true := by decide +kernel
private theorem c381696 : checkChunk 381696 128 = true := by decide +kernel
private theorem c381824 : checkChunk 381824 128 = true := by decide +kernel
private theorem c381952 : checkChunk 381952 128 = true := by decide +kernel
private theorem c382080 : checkChunk 382080 128 = true := by decide +kernel
private theorem c382208 : checkChunk 382208 128 = true := by decide +kernel
private theorem c382336 : checkChunk 382336 128 = true := by decide +kernel
private theorem c382464 : checkChunk 382464 128 = true := by decide +kernel
private theorem c382592 : checkChunk 382592 128 = true := by decide +kernel
private theorem c382720 : checkChunk 382720 128 = true := by decide +kernel
private theorem c382848 : checkChunk 382848 128 = true := by decide +kernel
private theorem c382976 : checkChunk 382976 128 = true := by decide +kernel
private theorem c383104 : checkChunk 383104 128 = true := by decide +kernel
private theorem c383232 : checkChunk 383232 128 = true := by decide +kernel
private theorem c383360 : checkChunk 383360 128 = true := by decide +kernel
private theorem c383488 : checkChunk 383488 128 = true := by decide +kernel
private theorem c383616 : checkChunk 383616 128 = true := by decide +kernel
private theorem c383744 : checkChunk 383744 128 = true := by decide +kernel
private theorem c383872 : checkChunk 383872 128 = true := by decide +kernel
private theorem c384000 : checkChunk 384000 128 = true := by decide +kernel
private theorem c384128 : checkChunk 384128 128 = true := by decide +kernel
private theorem c384256 : checkChunk 384256 128 = true := by decide +kernel
private theorem c384384 : checkChunk 384384 128 = true := by decide +kernel
private theorem c384512 : checkChunk 384512 128 = true := by decide +kernel
private theorem c384640 : checkChunk 384640 128 = true := by decide +kernel
private theorem c384768 : checkChunk 384768 128 = true := by decide +kernel
private theorem c384896 : checkChunk 384896 128 = true := by decide +kernel

public theorem checked : Checked 376832 385024 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 376832 128 c376832) (checkChunk_sound 376960 128 c376960)) (Checked.append (checkChunk_sound 377088 128 c377088) (checkChunk_sound 377216 128 c377216))) (Checked.append (Checked.append (checkChunk_sound 377344 128 c377344) (checkChunk_sound 377472 128 c377472)) (Checked.append (checkChunk_sound 377600 128 c377600) (checkChunk_sound 377728 128 c377728)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 377856 128 c377856) (checkChunk_sound 377984 128 c377984)) (Checked.append (checkChunk_sound 378112 128 c378112) (checkChunk_sound 378240 128 c378240))) (Checked.append (Checked.append (checkChunk_sound 378368 128 c378368) (checkChunk_sound 378496 128 c378496)) (Checked.append (checkChunk_sound 378624 128 c378624) (checkChunk_sound 378752 128 c378752))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 378880 128 c378880) (checkChunk_sound 379008 128 c379008)) (Checked.append (checkChunk_sound 379136 128 c379136) (checkChunk_sound 379264 128 c379264))) (Checked.append (Checked.append (checkChunk_sound 379392 128 c379392) (checkChunk_sound 379520 128 c379520)) (Checked.append (checkChunk_sound 379648 128 c379648) (checkChunk_sound 379776 128 c379776)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 379904 128 c379904) (checkChunk_sound 380032 128 c380032)) (Checked.append (checkChunk_sound 380160 128 c380160) (checkChunk_sound 380288 128 c380288))) (Checked.append (Checked.append (checkChunk_sound 380416 128 c380416) (checkChunk_sound 380544 128 c380544)) (Checked.append (checkChunk_sound 380672 128 c380672) (checkChunk_sound 380800 128 c380800)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 380928 128 c380928) (checkChunk_sound 381056 128 c381056)) (Checked.append (checkChunk_sound 381184 128 c381184) (checkChunk_sound 381312 128 c381312))) (Checked.append (Checked.append (checkChunk_sound 381440 128 c381440) (checkChunk_sound 381568 128 c381568)) (Checked.append (checkChunk_sound 381696 128 c381696) (checkChunk_sound 381824 128 c381824)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 381952 128 c381952) (checkChunk_sound 382080 128 c382080)) (Checked.append (checkChunk_sound 382208 128 c382208) (checkChunk_sound 382336 128 c382336))) (Checked.append (Checked.append (checkChunk_sound 382464 128 c382464) (checkChunk_sound 382592 128 c382592)) (Checked.append (checkChunk_sound 382720 128 c382720) (checkChunk_sound 382848 128 c382848))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 382976 128 c382976) (checkChunk_sound 383104 128 c383104)) (Checked.append (checkChunk_sound 383232 128 c383232) (checkChunk_sound 383360 128 c383360))) (Checked.append (Checked.append (checkChunk_sound 383488 128 c383488) (checkChunk_sound 383616 128 c383616)) (Checked.append (checkChunk_sound 383744 128 c383744) (checkChunk_sound 383872 128 c383872)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 384000 128 c384000) (checkChunk_sound 384128 128 c384128)) (Checked.append (checkChunk_sound 384256 128 c384256) (checkChunk_sound 384384 128 c384384))) (Checked.append (Checked.append (checkChunk_sound 384512 128 c384512) (checkChunk_sound 384640 128 c384640)) (Checked.append (checkChunk_sound 384768 128 c384768) (checkChunk_sound 384896 128 c384896)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B019
