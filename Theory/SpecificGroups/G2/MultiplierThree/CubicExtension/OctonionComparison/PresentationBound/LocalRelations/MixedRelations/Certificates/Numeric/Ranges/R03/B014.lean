module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [761856, 770048).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B014
private theorem c761856 : checkChunk 761856 128 = true := by decide +kernel
private theorem c761984 : checkChunk 761984 128 = true := by decide +kernel
private theorem c762112 : checkChunk 762112 128 = true := by decide +kernel
private theorem c762240 : checkChunk 762240 128 = true := by decide +kernel
private theorem c762368 : checkChunk 762368 128 = true := by decide +kernel
private theorem c762496 : checkChunk 762496 128 = true := by decide +kernel
private theorem c762624 : checkChunk 762624 128 = true := by decide +kernel
private theorem c762752 : checkChunk 762752 128 = true := by decide +kernel
private theorem c762880 : checkChunk 762880 128 = true := by decide +kernel
private theorem c763008 : checkChunk 763008 128 = true := by decide +kernel
private theorem c763136 : checkChunk 763136 128 = true := by decide +kernel
private theorem c763264 : checkChunk 763264 128 = true := by decide +kernel
private theorem c763392 : checkChunk 763392 128 = true := by decide +kernel
private theorem c763520 : checkChunk 763520 128 = true := by decide +kernel
private theorem c763648 : checkChunk 763648 128 = true := by decide +kernel
private theorem c763776 : checkChunk 763776 128 = true := by decide +kernel
private theorem c763904 : checkChunk 763904 128 = true := by decide +kernel
private theorem c764032 : checkChunk 764032 128 = true := by decide +kernel
private theorem c764160 : checkChunk 764160 128 = true := by decide +kernel
private theorem c764288 : checkChunk 764288 128 = true := by decide +kernel
private theorem c764416 : checkChunk 764416 128 = true := by decide +kernel
private theorem c764544 : checkChunk 764544 128 = true := by decide +kernel
private theorem c764672 : checkChunk 764672 128 = true := by decide +kernel
private theorem c764800 : checkChunk 764800 128 = true := by decide +kernel
private theorem c764928 : checkChunk 764928 128 = true := by decide +kernel
private theorem c765056 : checkChunk 765056 128 = true := by decide +kernel
private theorem c765184 : checkChunk 765184 128 = true := by decide +kernel
private theorem c765312 : checkChunk 765312 128 = true := by decide +kernel
private theorem c765440 : checkChunk 765440 128 = true := by decide +kernel
private theorem c765568 : checkChunk 765568 128 = true := by decide +kernel
private theorem c765696 : checkChunk 765696 128 = true := by decide +kernel
private theorem c765824 : checkChunk 765824 128 = true := by decide +kernel
private theorem c765952 : checkChunk 765952 128 = true := by decide +kernel
private theorem c766080 : checkChunk 766080 128 = true := by decide +kernel
private theorem c766208 : checkChunk 766208 128 = true := by decide +kernel
private theorem c766336 : checkChunk 766336 128 = true := by decide +kernel
private theorem c766464 : checkChunk 766464 128 = true := by decide +kernel
private theorem c766592 : checkChunk 766592 128 = true := by decide +kernel
private theorem c766720 : checkChunk 766720 128 = true := by decide +kernel
private theorem c766848 : checkChunk 766848 128 = true := by decide +kernel
private theorem c766976 : checkChunk 766976 128 = true := by decide +kernel
private theorem c767104 : checkChunk 767104 128 = true := by decide +kernel
private theorem c767232 : checkChunk 767232 128 = true := by decide +kernel
private theorem c767360 : checkChunk 767360 128 = true := by decide +kernel
private theorem c767488 : checkChunk 767488 128 = true := by decide +kernel
private theorem c767616 : checkChunk 767616 128 = true := by decide +kernel
private theorem c767744 : checkChunk 767744 128 = true := by decide +kernel
private theorem c767872 : checkChunk 767872 128 = true := by decide +kernel
private theorem c768000 : checkChunk 768000 128 = true := by decide +kernel
private theorem c768128 : checkChunk 768128 128 = true := by decide +kernel
private theorem c768256 : checkChunk 768256 128 = true := by decide +kernel
private theorem c768384 : checkChunk 768384 128 = true := by decide +kernel
private theorem c768512 : checkChunk 768512 128 = true := by decide +kernel
private theorem c768640 : checkChunk 768640 128 = true := by decide +kernel
private theorem c768768 : checkChunk 768768 128 = true := by decide +kernel
private theorem c768896 : checkChunk 768896 128 = true := by decide +kernel
private theorem c769024 : checkChunk 769024 128 = true := by decide +kernel
private theorem c769152 : checkChunk 769152 128 = true := by decide +kernel
private theorem c769280 : checkChunk 769280 128 = true := by decide +kernel
private theorem c769408 : checkChunk 769408 128 = true := by decide +kernel
private theorem c769536 : checkChunk 769536 128 = true := by decide +kernel
private theorem c769664 : checkChunk 769664 128 = true := by decide +kernel
private theorem c769792 : checkChunk 769792 128 = true := by decide +kernel
private theorem c769920 : checkChunk 769920 128 = true := by decide +kernel

public theorem checked : Checked 761856 770048 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 761856 128 c761856) (checkChunk_sound 761984 128 c761984)) (Checked.append (checkChunk_sound 762112 128 c762112) (checkChunk_sound 762240 128 c762240))) (Checked.append (Checked.append (checkChunk_sound 762368 128 c762368) (checkChunk_sound 762496 128 c762496)) (Checked.append (checkChunk_sound 762624 128 c762624) (checkChunk_sound 762752 128 c762752)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 762880 128 c762880) (checkChunk_sound 763008 128 c763008)) (Checked.append (checkChunk_sound 763136 128 c763136) (checkChunk_sound 763264 128 c763264))) (Checked.append (Checked.append (checkChunk_sound 763392 128 c763392) (checkChunk_sound 763520 128 c763520)) (Checked.append (checkChunk_sound 763648 128 c763648) (checkChunk_sound 763776 128 c763776))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 763904 128 c763904) (checkChunk_sound 764032 128 c764032)) (Checked.append (checkChunk_sound 764160 128 c764160) (checkChunk_sound 764288 128 c764288))) (Checked.append (Checked.append (checkChunk_sound 764416 128 c764416) (checkChunk_sound 764544 128 c764544)) (Checked.append (checkChunk_sound 764672 128 c764672) (checkChunk_sound 764800 128 c764800)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 764928 128 c764928) (checkChunk_sound 765056 128 c765056)) (Checked.append (checkChunk_sound 765184 128 c765184) (checkChunk_sound 765312 128 c765312))) (Checked.append (Checked.append (checkChunk_sound 765440 128 c765440) (checkChunk_sound 765568 128 c765568)) (Checked.append (checkChunk_sound 765696 128 c765696) (checkChunk_sound 765824 128 c765824)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 765952 128 c765952) (checkChunk_sound 766080 128 c766080)) (Checked.append (checkChunk_sound 766208 128 c766208) (checkChunk_sound 766336 128 c766336))) (Checked.append (Checked.append (checkChunk_sound 766464 128 c766464) (checkChunk_sound 766592 128 c766592)) (Checked.append (checkChunk_sound 766720 128 c766720) (checkChunk_sound 766848 128 c766848)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 766976 128 c766976) (checkChunk_sound 767104 128 c767104)) (Checked.append (checkChunk_sound 767232 128 c767232) (checkChunk_sound 767360 128 c767360))) (Checked.append (Checked.append (checkChunk_sound 767488 128 c767488) (checkChunk_sound 767616 128 c767616)) (Checked.append (checkChunk_sound 767744 128 c767744) (checkChunk_sound 767872 128 c767872))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 768000 128 c768000) (checkChunk_sound 768128 128 c768128)) (Checked.append (checkChunk_sound 768256 128 c768256) (checkChunk_sound 768384 128 c768384))) (Checked.append (Checked.append (checkChunk_sound 768512 128 c768512) (checkChunk_sound 768640 128 c768640)) (Checked.append (checkChunk_sound 768768 128 c768768) (checkChunk_sound 768896 128 c768896)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 769024 128 c769024) (checkChunk_sound 769152 128 c769152)) (Checked.append (checkChunk_sound 769280 128 c769280) (checkChunk_sound 769408 128 c769408))) (Checked.append (Checked.append (checkChunk_sound 769536 128 c769536) (checkChunk_sound 769664 128 c769664)) (Checked.append (checkChunk_sound 769792 128 c769792) (checkChunk_sound 769920 128 c769920)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B014
