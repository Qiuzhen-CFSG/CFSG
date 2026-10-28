module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [729088, 737280).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B010
private theorem c729088 : checkChunk 729088 128 = true := by decide +kernel
private theorem c729216 : checkChunk 729216 128 = true := by decide +kernel
private theorem c729344 : checkChunk 729344 128 = true := by decide +kernel
private theorem c729472 : checkChunk 729472 128 = true := by decide +kernel
private theorem c729600 : checkChunk 729600 128 = true := by decide +kernel
private theorem c729728 : checkChunk 729728 128 = true := by decide +kernel
private theorem c729856 : checkChunk 729856 128 = true := by decide +kernel
private theorem c729984 : checkChunk 729984 128 = true := by decide +kernel
private theorem c730112 : checkChunk 730112 128 = true := by decide +kernel
private theorem c730240 : checkChunk 730240 128 = true := by decide +kernel
private theorem c730368 : checkChunk 730368 128 = true := by decide +kernel
private theorem c730496 : checkChunk 730496 128 = true := by decide +kernel
private theorem c730624 : checkChunk 730624 128 = true := by decide +kernel
private theorem c730752 : checkChunk 730752 128 = true := by decide +kernel
private theorem c730880 : checkChunk 730880 128 = true := by decide +kernel
private theorem c731008 : checkChunk 731008 128 = true := by decide +kernel
private theorem c731136 : checkChunk 731136 128 = true := by decide +kernel
private theorem c731264 : checkChunk 731264 128 = true := by decide +kernel
private theorem c731392 : checkChunk 731392 128 = true := by decide +kernel
private theorem c731520 : checkChunk 731520 128 = true := by decide +kernel
private theorem c731648 : checkChunk 731648 128 = true := by decide +kernel
private theorem c731776 : checkChunk 731776 128 = true := by decide +kernel
private theorem c731904 : checkChunk 731904 128 = true := by decide +kernel
private theorem c732032 : checkChunk 732032 128 = true := by decide +kernel
private theorem c732160 : checkChunk 732160 128 = true := by decide +kernel
private theorem c732288 : checkChunk 732288 128 = true := by decide +kernel
private theorem c732416 : checkChunk 732416 128 = true := by decide +kernel
private theorem c732544 : checkChunk 732544 128 = true := by decide +kernel
private theorem c732672 : checkChunk 732672 128 = true := by decide +kernel
private theorem c732800 : checkChunk 732800 128 = true := by decide +kernel
private theorem c732928 : checkChunk 732928 128 = true := by decide +kernel
private theorem c733056 : checkChunk 733056 128 = true := by decide +kernel
private theorem c733184 : checkChunk 733184 128 = true := by decide +kernel
private theorem c733312 : checkChunk 733312 128 = true := by decide +kernel
private theorem c733440 : checkChunk 733440 128 = true := by decide +kernel
private theorem c733568 : checkChunk 733568 128 = true := by decide +kernel
private theorem c733696 : checkChunk 733696 128 = true := by decide +kernel
private theorem c733824 : checkChunk 733824 128 = true := by decide +kernel
private theorem c733952 : checkChunk 733952 128 = true := by decide +kernel
private theorem c734080 : checkChunk 734080 128 = true := by decide +kernel
private theorem c734208 : checkChunk 734208 128 = true := by decide +kernel
private theorem c734336 : checkChunk 734336 128 = true := by decide +kernel
private theorem c734464 : checkChunk 734464 128 = true := by decide +kernel
private theorem c734592 : checkChunk 734592 128 = true := by decide +kernel
private theorem c734720 : checkChunk 734720 128 = true := by decide +kernel
private theorem c734848 : checkChunk 734848 128 = true := by decide +kernel
private theorem c734976 : checkChunk 734976 128 = true := by decide +kernel
private theorem c735104 : checkChunk 735104 128 = true := by decide +kernel
private theorem c735232 : checkChunk 735232 128 = true := by decide +kernel
private theorem c735360 : checkChunk 735360 128 = true := by decide +kernel
private theorem c735488 : checkChunk 735488 128 = true := by decide +kernel
private theorem c735616 : checkChunk 735616 128 = true := by decide +kernel
private theorem c735744 : checkChunk 735744 128 = true := by decide +kernel
private theorem c735872 : checkChunk 735872 128 = true := by decide +kernel
private theorem c736000 : checkChunk 736000 128 = true := by decide +kernel
private theorem c736128 : checkChunk 736128 128 = true := by decide +kernel
private theorem c736256 : checkChunk 736256 128 = true := by decide +kernel
private theorem c736384 : checkChunk 736384 128 = true := by decide +kernel
private theorem c736512 : checkChunk 736512 128 = true := by decide +kernel
private theorem c736640 : checkChunk 736640 128 = true := by decide +kernel
private theorem c736768 : checkChunk 736768 128 = true := by decide +kernel
private theorem c736896 : checkChunk 736896 128 = true := by decide +kernel
private theorem c737024 : checkChunk 737024 128 = true := by decide +kernel
private theorem c737152 : checkChunk 737152 128 = true := by decide +kernel

public theorem checked : Checked 729088 737280 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 729088 128 c729088) (checkChunk_sound 729216 128 c729216)) (Checked.append (checkChunk_sound 729344 128 c729344) (checkChunk_sound 729472 128 c729472))) (Checked.append (Checked.append (checkChunk_sound 729600 128 c729600) (checkChunk_sound 729728 128 c729728)) (Checked.append (checkChunk_sound 729856 128 c729856) (checkChunk_sound 729984 128 c729984)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 730112 128 c730112) (checkChunk_sound 730240 128 c730240)) (Checked.append (checkChunk_sound 730368 128 c730368) (checkChunk_sound 730496 128 c730496))) (Checked.append (Checked.append (checkChunk_sound 730624 128 c730624) (checkChunk_sound 730752 128 c730752)) (Checked.append (checkChunk_sound 730880 128 c730880) (checkChunk_sound 731008 128 c731008))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 731136 128 c731136) (checkChunk_sound 731264 128 c731264)) (Checked.append (checkChunk_sound 731392 128 c731392) (checkChunk_sound 731520 128 c731520))) (Checked.append (Checked.append (checkChunk_sound 731648 128 c731648) (checkChunk_sound 731776 128 c731776)) (Checked.append (checkChunk_sound 731904 128 c731904) (checkChunk_sound 732032 128 c732032)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 732160 128 c732160) (checkChunk_sound 732288 128 c732288)) (Checked.append (checkChunk_sound 732416 128 c732416) (checkChunk_sound 732544 128 c732544))) (Checked.append (Checked.append (checkChunk_sound 732672 128 c732672) (checkChunk_sound 732800 128 c732800)) (Checked.append (checkChunk_sound 732928 128 c732928) (checkChunk_sound 733056 128 c733056)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 733184 128 c733184) (checkChunk_sound 733312 128 c733312)) (Checked.append (checkChunk_sound 733440 128 c733440) (checkChunk_sound 733568 128 c733568))) (Checked.append (Checked.append (checkChunk_sound 733696 128 c733696) (checkChunk_sound 733824 128 c733824)) (Checked.append (checkChunk_sound 733952 128 c733952) (checkChunk_sound 734080 128 c734080)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 734208 128 c734208) (checkChunk_sound 734336 128 c734336)) (Checked.append (checkChunk_sound 734464 128 c734464) (checkChunk_sound 734592 128 c734592))) (Checked.append (Checked.append (checkChunk_sound 734720 128 c734720) (checkChunk_sound 734848 128 c734848)) (Checked.append (checkChunk_sound 734976 128 c734976) (checkChunk_sound 735104 128 c735104))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 735232 128 c735232) (checkChunk_sound 735360 128 c735360)) (Checked.append (checkChunk_sound 735488 128 c735488) (checkChunk_sound 735616 128 c735616))) (Checked.append (Checked.append (checkChunk_sound 735744 128 c735744) (checkChunk_sound 735872 128 c735872)) (Checked.append (checkChunk_sound 736000 128 c736000) (checkChunk_sound 736128 128 c736128)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 736256 128 c736256) (checkChunk_sound 736384 128 c736384)) (Checked.append (checkChunk_sound 736512 128 c736512) (checkChunk_sound 736640 128 c736640))) (Checked.append (Checked.append (checkChunk_sound 736768 128 c736768) (checkChunk_sound 736896 128 c736896)) (Checked.append (checkChunk_sound 737024 128 c737024) (checkChunk_sound 737152 128 c737152)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B010
