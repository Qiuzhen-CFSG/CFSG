module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [450560, 458752).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B002
private theorem c450560 : checkChunk 450560 128 = true := by decide +kernel
private theorem c450688 : checkChunk 450688 128 = true := by decide +kernel
private theorem c450816 : checkChunk 450816 128 = true := by decide +kernel
private theorem c450944 : checkChunk 450944 128 = true := by decide +kernel
private theorem c451072 : checkChunk 451072 128 = true := by decide +kernel
private theorem c451200 : checkChunk 451200 128 = true := by decide +kernel
private theorem c451328 : checkChunk 451328 128 = true := by decide +kernel
private theorem c451456 : checkChunk 451456 128 = true := by decide +kernel
private theorem c451584 : checkChunk 451584 128 = true := by decide +kernel
private theorem c451712 : checkChunk 451712 128 = true := by decide +kernel
private theorem c451840 : checkChunk 451840 128 = true := by decide +kernel
private theorem c451968 : checkChunk 451968 128 = true := by decide +kernel
private theorem c452096 : checkChunk 452096 128 = true := by decide +kernel
private theorem c452224 : checkChunk 452224 128 = true := by decide +kernel
private theorem c452352 : checkChunk 452352 128 = true := by decide +kernel
private theorem c452480 : checkChunk 452480 128 = true := by decide +kernel
private theorem c452608 : checkChunk 452608 128 = true := by decide +kernel
private theorem c452736 : checkChunk 452736 128 = true := by decide +kernel
private theorem c452864 : checkChunk 452864 128 = true := by decide +kernel
private theorem c452992 : checkChunk 452992 128 = true := by decide +kernel
private theorem c453120 : checkChunk 453120 128 = true := by decide +kernel
private theorem c453248 : checkChunk 453248 128 = true := by decide +kernel
private theorem c453376 : checkChunk 453376 128 = true := by decide +kernel
private theorem c453504 : checkChunk 453504 128 = true := by decide +kernel
private theorem c453632 : checkChunk 453632 128 = true := by decide +kernel
private theorem c453760 : checkChunk 453760 128 = true := by decide +kernel
private theorem c453888 : checkChunk 453888 128 = true := by decide +kernel
private theorem c454016 : checkChunk 454016 128 = true := by decide +kernel
private theorem c454144 : checkChunk 454144 128 = true := by decide +kernel
private theorem c454272 : checkChunk 454272 128 = true := by decide +kernel
private theorem c454400 : checkChunk 454400 128 = true := by decide +kernel
private theorem c454528 : checkChunk 454528 128 = true := by decide +kernel
private theorem c454656 : checkChunk 454656 128 = true := by decide +kernel
private theorem c454784 : checkChunk 454784 128 = true := by decide +kernel
private theorem c454912 : checkChunk 454912 128 = true := by decide +kernel
private theorem c455040 : checkChunk 455040 128 = true := by decide +kernel
private theorem c455168 : checkChunk 455168 128 = true := by decide +kernel
private theorem c455296 : checkChunk 455296 128 = true := by decide +kernel
private theorem c455424 : checkChunk 455424 128 = true := by decide +kernel
private theorem c455552 : checkChunk 455552 128 = true := by decide +kernel
private theorem c455680 : checkChunk 455680 128 = true := by decide +kernel
private theorem c455808 : checkChunk 455808 128 = true := by decide +kernel
private theorem c455936 : checkChunk 455936 128 = true := by decide +kernel
private theorem c456064 : checkChunk 456064 128 = true := by decide +kernel
private theorem c456192 : checkChunk 456192 128 = true := by decide +kernel
private theorem c456320 : checkChunk 456320 128 = true := by decide +kernel
private theorem c456448 : checkChunk 456448 128 = true := by decide +kernel
private theorem c456576 : checkChunk 456576 128 = true := by decide +kernel
private theorem c456704 : checkChunk 456704 128 = true := by decide +kernel
private theorem c456832 : checkChunk 456832 128 = true := by decide +kernel
private theorem c456960 : checkChunk 456960 128 = true := by decide +kernel
private theorem c457088 : checkChunk 457088 128 = true := by decide +kernel
private theorem c457216 : checkChunk 457216 128 = true := by decide +kernel
private theorem c457344 : checkChunk 457344 128 = true := by decide +kernel
private theorem c457472 : checkChunk 457472 128 = true := by decide +kernel
private theorem c457600 : checkChunk 457600 128 = true := by decide +kernel
private theorem c457728 : checkChunk 457728 128 = true := by decide +kernel
private theorem c457856 : checkChunk 457856 128 = true := by decide +kernel
private theorem c457984 : checkChunk 457984 128 = true := by decide +kernel
private theorem c458112 : checkChunk 458112 128 = true := by decide +kernel
private theorem c458240 : checkChunk 458240 128 = true := by decide +kernel
private theorem c458368 : checkChunk 458368 128 = true := by decide +kernel
private theorem c458496 : checkChunk 458496 128 = true := by decide +kernel
private theorem c458624 : checkChunk 458624 128 = true := by decide +kernel

public theorem checked : Checked 450560 458752 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 450560 128 c450560) (checkChunk_sound 450688 128 c450688)) (Checked.append (checkChunk_sound 450816 128 c450816) (checkChunk_sound 450944 128 c450944))) (Checked.append (Checked.append (checkChunk_sound 451072 128 c451072) (checkChunk_sound 451200 128 c451200)) (Checked.append (checkChunk_sound 451328 128 c451328) (checkChunk_sound 451456 128 c451456)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 451584 128 c451584) (checkChunk_sound 451712 128 c451712)) (Checked.append (checkChunk_sound 451840 128 c451840) (checkChunk_sound 451968 128 c451968))) (Checked.append (Checked.append (checkChunk_sound 452096 128 c452096) (checkChunk_sound 452224 128 c452224)) (Checked.append (checkChunk_sound 452352 128 c452352) (checkChunk_sound 452480 128 c452480))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 452608 128 c452608) (checkChunk_sound 452736 128 c452736)) (Checked.append (checkChunk_sound 452864 128 c452864) (checkChunk_sound 452992 128 c452992))) (Checked.append (Checked.append (checkChunk_sound 453120 128 c453120) (checkChunk_sound 453248 128 c453248)) (Checked.append (checkChunk_sound 453376 128 c453376) (checkChunk_sound 453504 128 c453504)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 453632 128 c453632) (checkChunk_sound 453760 128 c453760)) (Checked.append (checkChunk_sound 453888 128 c453888) (checkChunk_sound 454016 128 c454016))) (Checked.append (Checked.append (checkChunk_sound 454144 128 c454144) (checkChunk_sound 454272 128 c454272)) (Checked.append (checkChunk_sound 454400 128 c454400) (checkChunk_sound 454528 128 c454528)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 454656 128 c454656) (checkChunk_sound 454784 128 c454784)) (Checked.append (checkChunk_sound 454912 128 c454912) (checkChunk_sound 455040 128 c455040))) (Checked.append (Checked.append (checkChunk_sound 455168 128 c455168) (checkChunk_sound 455296 128 c455296)) (Checked.append (checkChunk_sound 455424 128 c455424) (checkChunk_sound 455552 128 c455552)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 455680 128 c455680) (checkChunk_sound 455808 128 c455808)) (Checked.append (checkChunk_sound 455936 128 c455936) (checkChunk_sound 456064 128 c456064))) (Checked.append (Checked.append (checkChunk_sound 456192 128 c456192) (checkChunk_sound 456320 128 c456320)) (Checked.append (checkChunk_sound 456448 128 c456448) (checkChunk_sound 456576 128 c456576))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 456704 128 c456704) (checkChunk_sound 456832 128 c456832)) (Checked.append (checkChunk_sound 456960 128 c456960) (checkChunk_sound 457088 128 c457088))) (Checked.append (Checked.append (checkChunk_sound 457216 128 c457216) (checkChunk_sound 457344 128 c457344)) (Checked.append (checkChunk_sound 457472 128 c457472) (checkChunk_sound 457600 128 c457600)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 457728 128 c457728) (checkChunk_sound 457856 128 c457856)) (Checked.append (checkChunk_sound 457984 128 c457984) (checkChunk_sound 458112 128 c458112))) (Checked.append (Checked.append (checkChunk_sound 458240 128 c458240) (checkChunk_sound 458368 128 c458368)) (Checked.append (checkChunk_sound 458496 128 c458496) (checkChunk_sound 458624 128 c458624)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B002
