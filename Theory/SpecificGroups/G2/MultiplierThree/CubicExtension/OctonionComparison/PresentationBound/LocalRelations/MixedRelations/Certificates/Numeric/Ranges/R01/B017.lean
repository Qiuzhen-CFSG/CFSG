module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [360448, 368640).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B017
private theorem c360448 : checkChunk 360448 128 = true := by decide +kernel
private theorem c360576 : checkChunk 360576 128 = true := by decide +kernel
private theorem c360704 : checkChunk 360704 128 = true := by decide +kernel
private theorem c360832 : checkChunk 360832 128 = true := by decide +kernel
private theorem c360960 : checkChunk 360960 128 = true := by decide +kernel
private theorem c361088 : checkChunk 361088 128 = true := by decide +kernel
private theorem c361216 : checkChunk 361216 128 = true := by decide +kernel
private theorem c361344 : checkChunk 361344 128 = true := by decide +kernel
private theorem c361472 : checkChunk 361472 128 = true := by decide +kernel
private theorem c361600 : checkChunk 361600 128 = true := by decide +kernel
private theorem c361728 : checkChunk 361728 128 = true := by decide +kernel
private theorem c361856 : checkChunk 361856 128 = true := by decide +kernel
private theorem c361984 : checkChunk 361984 128 = true := by decide +kernel
private theorem c362112 : checkChunk 362112 128 = true := by decide +kernel
private theorem c362240 : checkChunk 362240 128 = true := by decide +kernel
private theorem c362368 : checkChunk 362368 128 = true := by decide +kernel
private theorem c362496 : checkChunk 362496 128 = true := by decide +kernel
private theorem c362624 : checkChunk 362624 128 = true := by decide +kernel
private theorem c362752 : checkChunk 362752 128 = true := by decide +kernel
private theorem c362880 : checkChunk 362880 128 = true := by decide +kernel
private theorem c363008 : checkChunk 363008 128 = true := by decide +kernel
private theorem c363136 : checkChunk 363136 128 = true := by decide +kernel
private theorem c363264 : checkChunk 363264 128 = true := by decide +kernel
private theorem c363392 : checkChunk 363392 128 = true := by decide +kernel
private theorem c363520 : checkChunk 363520 128 = true := by decide +kernel
private theorem c363648 : checkChunk 363648 128 = true := by decide +kernel
private theorem c363776 : checkChunk 363776 128 = true := by decide +kernel
private theorem c363904 : checkChunk 363904 128 = true := by decide +kernel
private theorem c364032 : checkChunk 364032 128 = true := by decide +kernel
private theorem c364160 : checkChunk 364160 128 = true := by decide +kernel
private theorem c364288 : checkChunk 364288 128 = true := by decide +kernel
private theorem c364416 : checkChunk 364416 128 = true := by decide +kernel
private theorem c364544 : checkChunk 364544 128 = true := by decide +kernel
private theorem c364672 : checkChunk 364672 128 = true := by decide +kernel
private theorem c364800 : checkChunk 364800 128 = true := by decide +kernel
private theorem c364928 : checkChunk 364928 128 = true := by decide +kernel
private theorem c365056 : checkChunk 365056 128 = true := by decide +kernel
private theorem c365184 : checkChunk 365184 128 = true := by decide +kernel
private theorem c365312 : checkChunk 365312 128 = true := by decide +kernel
private theorem c365440 : checkChunk 365440 128 = true := by decide +kernel
private theorem c365568 : checkChunk 365568 128 = true := by decide +kernel
private theorem c365696 : checkChunk 365696 128 = true := by decide +kernel
private theorem c365824 : checkChunk 365824 128 = true := by decide +kernel
private theorem c365952 : checkChunk 365952 128 = true := by decide +kernel
private theorem c366080 : checkChunk 366080 128 = true := by decide +kernel
private theorem c366208 : checkChunk 366208 128 = true := by decide +kernel
private theorem c366336 : checkChunk 366336 128 = true := by decide +kernel
private theorem c366464 : checkChunk 366464 128 = true := by decide +kernel
private theorem c366592 : checkChunk 366592 128 = true := by decide +kernel
private theorem c366720 : checkChunk 366720 128 = true := by decide +kernel
private theorem c366848 : checkChunk 366848 128 = true := by decide +kernel
private theorem c366976 : checkChunk 366976 128 = true := by decide +kernel
private theorem c367104 : checkChunk 367104 128 = true := by decide +kernel
private theorem c367232 : checkChunk 367232 128 = true := by decide +kernel
private theorem c367360 : checkChunk 367360 128 = true := by decide +kernel
private theorem c367488 : checkChunk 367488 128 = true := by decide +kernel
private theorem c367616 : checkChunk 367616 128 = true := by decide +kernel
private theorem c367744 : checkChunk 367744 128 = true := by decide +kernel
private theorem c367872 : checkChunk 367872 128 = true := by decide +kernel
private theorem c368000 : checkChunk 368000 128 = true := by decide +kernel
private theorem c368128 : checkChunk 368128 128 = true := by decide +kernel
private theorem c368256 : checkChunk 368256 128 = true := by decide +kernel
private theorem c368384 : checkChunk 368384 128 = true := by decide +kernel
private theorem c368512 : checkChunk 368512 128 = true := by decide +kernel

public theorem checked : Checked 360448 368640 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 360448 128 c360448) (checkChunk_sound 360576 128 c360576)) (Checked.append (checkChunk_sound 360704 128 c360704) (checkChunk_sound 360832 128 c360832))) (Checked.append (Checked.append (checkChunk_sound 360960 128 c360960) (checkChunk_sound 361088 128 c361088)) (Checked.append (checkChunk_sound 361216 128 c361216) (checkChunk_sound 361344 128 c361344)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 361472 128 c361472) (checkChunk_sound 361600 128 c361600)) (Checked.append (checkChunk_sound 361728 128 c361728) (checkChunk_sound 361856 128 c361856))) (Checked.append (Checked.append (checkChunk_sound 361984 128 c361984) (checkChunk_sound 362112 128 c362112)) (Checked.append (checkChunk_sound 362240 128 c362240) (checkChunk_sound 362368 128 c362368))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 362496 128 c362496) (checkChunk_sound 362624 128 c362624)) (Checked.append (checkChunk_sound 362752 128 c362752) (checkChunk_sound 362880 128 c362880))) (Checked.append (Checked.append (checkChunk_sound 363008 128 c363008) (checkChunk_sound 363136 128 c363136)) (Checked.append (checkChunk_sound 363264 128 c363264) (checkChunk_sound 363392 128 c363392)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 363520 128 c363520) (checkChunk_sound 363648 128 c363648)) (Checked.append (checkChunk_sound 363776 128 c363776) (checkChunk_sound 363904 128 c363904))) (Checked.append (Checked.append (checkChunk_sound 364032 128 c364032) (checkChunk_sound 364160 128 c364160)) (Checked.append (checkChunk_sound 364288 128 c364288) (checkChunk_sound 364416 128 c364416)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 364544 128 c364544) (checkChunk_sound 364672 128 c364672)) (Checked.append (checkChunk_sound 364800 128 c364800) (checkChunk_sound 364928 128 c364928))) (Checked.append (Checked.append (checkChunk_sound 365056 128 c365056) (checkChunk_sound 365184 128 c365184)) (Checked.append (checkChunk_sound 365312 128 c365312) (checkChunk_sound 365440 128 c365440)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 365568 128 c365568) (checkChunk_sound 365696 128 c365696)) (Checked.append (checkChunk_sound 365824 128 c365824) (checkChunk_sound 365952 128 c365952))) (Checked.append (Checked.append (checkChunk_sound 366080 128 c366080) (checkChunk_sound 366208 128 c366208)) (Checked.append (checkChunk_sound 366336 128 c366336) (checkChunk_sound 366464 128 c366464))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 366592 128 c366592) (checkChunk_sound 366720 128 c366720)) (Checked.append (checkChunk_sound 366848 128 c366848) (checkChunk_sound 366976 128 c366976))) (Checked.append (Checked.append (checkChunk_sound 367104 128 c367104) (checkChunk_sound 367232 128 c367232)) (Checked.append (checkChunk_sound 367360 128 c367360) (checkChunk_sound 367488 128 c367488)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 367616 128 c367616) (checkChunk_sound 367744 128 c367744)) (Checked.append (checkChunk_sound 367872 128 c367872) (checkChunk_sound 368000 128 c368000))) (Checked.append (Checked.append (checkChunk_sound 368128 128 c368128) (checkChunk_sound 368256 128 c368256)) (Checked.append (checkChunk_sound 368384 128 c368384) (checkChunk_sound 368512 128 c368512)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B017
