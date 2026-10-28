module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [327680, 335872).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B013
private theorem c327680 : checkChunk 327680 128 = true := by decide +kernel
private theorem c327808 : checkChunk 327808 128 = true := by decide +kernel
private theorem c327936 : checkChunk 327936 128 = true := by decide +kernel
private theorem c328064 : checkChunk 328064 128 = true := by decide +kernel
private theorem c328192 : checkChunk 328192 128 = true := by decide +kernel
private theorem c328320 : checkChunk 328320 128 = true := by decide +kernel
private theorem c328448 : checkChunk 328448 128 = true := by decide +kernel
private theorem c328576 : checkChunk 328576 128 = true := by decide +kernel
private theorem c328704 : checkChunk 328704 128 = true := by decide +kernel
private theorem c328832 : checkChunk 328832 128 = true := by decide +kernel
private theorem c328960 : checkChunk 328960 128 = true := by decide +kernel
private theorem c329088 : checkChunk 329088 128 = true := by decide +kernel
private theorem c329216 : checkChunk 329216 128 = true := by decide +kernel
private theorem c329344 : checkChunk 329344 128 = true := by decide +kernel
private theorem c329472 : checkChunk 329472 128 = true := by decide +kernel
private theorem c329600 : checkChunk 329600 128 = true := by decide +kernel
private theorem c329728 : checkChunk 329728 128 = true := by decide +kernel
private theorem c329856 : checkChunk 329856 128 = true := by decide +kernel
private theorem c329984 : checkChunk 329984 128 = true := by decide +kernel
private theorem c330112 : checkChunk 330112 128 = true := by decide +kernel
private theorem c330240 : checkChunk 330240 128 = true := by decide +kernel
private theorem c330368 : checkChunk 330368 128 = true := by decide +kernel
private theorem c330496 : checkChunk 330496 128 = true := by decide +kernel
private theorem c330624 : checkChunk 330624 128 = true := by decide +kernel
private theorem c330752 : checkChunk 330752 128 = true := by decide +kernel
private theorem c330880 : checkChunk 330880 128 = true := by decide +kernel
private theorem c331008 : checkChunk 331008 128 = true := by decide +kernel
private theorem c331136 : checkChunk 331136 128 = true := by decide +kernel
private theorem c331264 : checkChunk 331264 128 = true := by decide +kernel
private theorem c331392 : checkChunk 331392 128 = true := by decide +kernel
private theorem c331520 : checkChunk 331520 128 = true := by decide +kernel
private theorem c331648 : checkChunk 331648 128 = true := by decide +kernel
private theorem c331776 : checkChunk 331776 128 = true := by decide +kernel
private theorem c331904 : checkChunk 331904 128 = true := by decide +kernel
private theorem c332032 : checkChunk 332032 128 = true := by decide +kernel
private theorem c332160 : checkChunk 332160 128 = true := by decide +kernel
private theorem c332288 : checkChunk 332288 128 = true := by decide +kernel
private theorem c332416 : checkChunk 332416 128 = true := by decide +kernel
private theorem c332544 : checkChunk 332544 128 = true := by decide +kernel
private theorem c332672 : checkChunk 332672 128 = true := by decide +kernel
private theorem c332800 : checkChunk 332800 128 = true := by decide +kernel
private theorem c332928 : checkChunk 332928 128 = true := by decide +kernel
private theorem c333056 : checkChunk 333056 128 = true := by decide +kernel
private theorem c333184 : checkChunk 333184 128 = true := by decide +kernel
private theorem c333312 : checkChunk 333312 128 = true := by decide +kernel
private theorem c333440 : checkChunk 333440 128 = true := by decide +kernel
private theorem c333568 : checkChunk 333568 128 = true := by decide +kernel
private theorem c333696 : checkChunk 333696 128 = true := by decide +kernel
private theorem c333824 : checkChunk 333824 128 = true := by decide +kernel
private theorem c333952 : checkChunk 333952 128 = true := by decide +kernel
private theorem c334080 : checkChunk 334080 128 = true := by decide +kernel
private theorem c334208 : checkChunk 334208 128 = true := by decide +kernel
private theorem c334336 : checkChunk 334336 128 = true := by decide +kernel
private theorem c334464 : checkChunk 334464 128 = true := by decide +kernel
private theorem c334592 : checkChunk 334592 128 = true := by decide +kernel
private theorem c334720 : checkChunk 334720 128 = true := by decide +kernel
private theorem c334848 : checkChunk 334848 128 = true := by decide +kernel
private theorem c334976 : checkChunk 334976 128 = true := by decide +kernel
private theorem c335104 : checkChunk 335104 128 = true := by decide +kernel
private theorem c335232 : checkChunk 335232 128 = true := by decide +kernel
private theorem c335360 : checkChunk 335360 128 = true := by decide +kernel
private theorem c335488 : checkChunk 335488 128 = true := by decide +kernel
private theorem c335616 : checkChunk 335616 128 = true := by decide +kernel
private theorem c335744 : checkChunk 335744 128 = true := by decide +kernel

public theorem checked : Checked 327680 335872 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 327680 128 c327680) (checkChunk_sound 327808 128 c327808)) (Checked.append (checkChunk_sound 327936 128 c327936) (checkChunk_sound 328064 128 c328064))) (Checked.append (Checked.append (checkChunk_sound 328192 128 c328192) (checkChunk_sound 328320 128 c328320)) (Checked.append (checkChunk_sound 328448 128 c328448) (checkChunk_sound 328576 128 c328576)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 328704 128 c328704) (checkChunk_sound 328832 128 c328832)) (Checked.append (checkChunk_sound 328960 128 c328960) (checkChunk_sound 329088 128 c329088))) (Checked.append (Checked.append (checkChunk_sound 329216 128 c329216) (checkChunk_sound 329344 128 c329344)) (Checked.append (checkChunk_sound 329472 128 c329472) (checkChunk_sound 329600 128 c329600))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 329728 128 c329728) (checkChunk_sound 329856 128 c329856)) (Checked.append (checkChunk_sound 329984 128 c329984) (checkChunk_sound 330112 128 c330112))) (Checked.append (Checked.append (checkChunk_sound 330240 128 c330240) (checkChunk_sound 330368 128 c330368)) (Checked.append (checkChunk_sound 330496 128 c330496) (checkChunk_sound 330624 128 c330624)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 330752 128 c330752) (checkChunk_sound 330880 128 c330880)) (Checked.append (checkChunk_sound 331008 128 c331008) (checkChunk_sound 331136 128 c331136))) (Checked.append (Checked.append (checkChunk_sound 331264 128 c331264) (checkChunk_sound 331392 128 c331392)) (Checked.append (checkChunk_sound 331520 128 c331520) (checkChunk_sound 331648 128 c331648)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 331776 128 c331776) (checkChunk_sound 331904 128 c331904)) (Checked.append (checkChunk_sound 332032 128 c332032) (checkChunk_sound 332160 128 c332160))) (Checked.append (Checked.append (checkChunk_sound 332288 128 c332288) (checkChunk_sound 332416 128 c332416)) (Checked.append (checkChunk_sound 332544 128 c332544) (checkChunk_sound 332672 128 c332672)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 332800 128 c332800) (checkChunk_sound 332928 128 c332928)) (Checked.append (checkChunk_sound 333056 128 c333056) (checkChunk_sound 333184 128 c333184))) (Checked.append (Checked.append (checkChunk_sound 333312 128 c333312) (checkChunk_sound 333440 128 c333440)) (Checked.append (checkChunk_sound 333568 128 c333568) (checkChunk_sound 333696 128 c333696))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 333824 128 c333824) (checkChunk_sound 333952 128 c333952)) (Checked.append (checkChunk_sound 334080 128 c334080) (checkChunk_sound 334208 128 c334208))) (Checked.append (Checked.append (checkChunk_sound 334336 128 c334336) (checkChunk_sound 334464 128 c334464)) (Checked.append (checkChunk_sound 334592 128 c334592) (checkChunk_sound 334720 128 c334720)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 334848 128 c334848) (checkChunk_sound 334976 128 c334976)) (Checked.append (checkChunk_sound 335104 128 c335104) (checkChunk_sound 335232 128 c335232))) (Checked.append (Checked.append (checkChunk_sound 335360 128 c335360) (checkChunk_sound 335488 128 c335488)) (Checked.append (checkChunk_sound 335616 128 c335616) (checkChunk_sound 335744 128 c335744)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B013
