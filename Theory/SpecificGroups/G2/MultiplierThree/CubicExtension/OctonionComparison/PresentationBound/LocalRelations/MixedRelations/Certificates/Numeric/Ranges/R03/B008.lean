module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [712704, 720896).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B008
private theorem c712704 : checkChunk 712704 128 = true := by decide +kernel
private theorem c712832 : checkChunk 712832 128 = true := by decide +kernel
private theorem c712960 : checkChunk 712960 128 = true := by decide +kernel
private theorem c713088 : checkChunk 713088 128 = true := by decide +kernel
private theorem c713216 : checkChunk 713216 128 = true := by decide +kernel
private theorem c713344 : checkChunk 713344 128 = true := by decide +kernel
private theorem c713472 : checkChunk 713472 128 = true := by decide +kernel
private theorem c713600 : checkChunk 713600 128 = true := by decide +kernel
private theorem c713728 : checkChunk 713728 128 = true := by decide +kernel
private theorem c713856 : checkChunk 713856 128 = true := by decide +kernel
private theorem c713984 : checkChunk 713984 128 = true := by decide +kernel
private theorem c714112 : checkChunk 714112 128 = true := by decide +kernel
private theorem c714240 : checkChunk 714240 128 = true := by decide +kernel
private theorem c714368 : checkChunk 714368 128 = true := by decide +kernel
private theorem c714496 : checkChunk 714496 128 = true := by decide +kernel
private theorem c714624 : checkChunk 714624 128 = true := by decide +kernel
private theorem c714752 : checkChunk 714752 128 = true := by decide +kernel
private theorem c714880 : checkChunk 714880 128 = true := by decide +kernel
private theorem c715008 : checkChunk 715008 128 = true := by decide +kernel
private theorem c715136 : checkChunk 715136 128 = true := by decide +kernel
private theorem c715264 : checkChunk 715264 128 = true := by decide +kernel
private theorem c715392 : checkChunk 715392 128 = true := by decide +kernel
private theorem c715520 : checkChunk 715520 128 = true := by decide +kernel
private theorem c715648 : checkChunk 715648 128 = true := by decide +kernel
private theorem c715776 : checkChunk 715776 128 = true := by decide +kernel
private theorem c715904 : checkChunk 715904 128 = true := by decide +kernel
private theorem c716032 : checkChunk 716032 128 = true := by decide +kernel
private theorem c716160 : checkChunk 716160 128 = true := by decide +kernel
private theorem c716288 : checkChunk 716288 128 = true := by decide +kernel
private theorem c716416 : checkChunk 716416 128 = true := by decide +kernel
private theorem c716544 : checkChunk 716544 128 = true := by decide +kernel
private theorem c716672 : checkChunk 716672 128 = true := by decide +kernel
private theorem c716800 : checkChunk 716800 128 = true := by decide +kernel
private theorem c716928 : checkChunk 716928 128 = true := by decide +kernel
private theorem c717056 : checkChunk 717056 128 = true := by decide +kernel
private theorem c717184 : checkChunk 717184 128 = true := by decide +kernel
private theorem c717312 : checkChunk 717312 128 = true := by decide +kernel
private theorem c717440 : checkChunk 717440 128 = true := by decide +kernel
private theorem c717568 : checkChunk 717568 128 = true := by decide +kernel
private theorem c717696 : checkChunk 717696 128 = true := by decide +kernel
private theorem c717824 : checkChunk 717824 128 = true := by decide +kernel
private theorem c717952 : checkChunk 717952 128 = true := by decide +kernel
private theorem c718080 : checkChunk 718080 128 = true := by decide +kernel
private theorem c718208 : checkChunk 718208 128 = true := by decide +kernel
private theorem c718336 : checkChunk 718336 128 = true := by decide +kernel
private theorem c718464 : checkChunk 718464 128 = true := by decide +kernel
private theorem c718592 : checkChunk 718592 128 = true := by decide +kernel
private theorem c718720 : checkChunk 718720 128 = true := by decide +kernel
private theorem c718848 : checkChunk 718848 128 = true := by decide +kernel
private theorem c718976 : checkChunk 718976 128 = true := by decide +kernel
private theorem c719104 : checkChunk 719104 128 = true := by decide +kernel
private theorem c719232 : checkChunk 719232 128 = true := by decide +kernel
private theorem c719360 : checkChunk 719360 128 = true := by decide +kernel
private theorem c719488 : checkChunk 719488 128 = true := by decide +kernel
private theorem c719616 : checkChunk 719616 128 = true := by decide +kernel
private theorem c719744 : checkChunk 719744 128 = true := by decide +kernel
private theorem c719872 : checkChunk 719872 128 = true := by decide +kernel
private theorem c720000 : checkChunk 720000 128 = true := by decide +kernel
private theorem c720128 : checkChunk 720128 128 = true := by decide +kernel
private theorem c720256 : checkChunk 720256 128 = true := by decide +kernel
private theorem c720384 : checkChunk 720384 128 = true := by decide +kernel
private theorem c720512 : checkChunk 720512 128 = true := by decide +kernel
private theorem c720640 : checkChunk 720640 128 = true := by decide +kernel
private theorem c720768 : checkChunk 720768 128 = true := by decide +kernel

public theorem checked : Checked 712704 720896 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 712704 128 c712704) (checkChunk_sound 712832 128 c712832)) (Checked.append (checkChunk_sound 712960 128 c712960) (checkChunk_sound 713088 128 c713088))) (Checked.append (Checked.append (checkChunk_sound 713216 128 c713216) (checkChunk_sound 713344 128 c713344)) (Checked.append (checkChunk_sound 713472 128 c713472) (checkChunk_sound 713600 128 c713600)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 713728 128 c713728) (checkChunk_sound 713856 128 c713856)) (Checked.append (checkChunk_sound 713984 128 c713984) (checkChunk_sound 714112 128 c714112))) (Checked.append (Checked.append (checkChunk_sound 714240 128 c714240) (checkChunk_sound 714368 128 c714368)) (Checked.append (checkChunk_sound 714496 128 c714496) (checkChunk_sound 714624 128 c714624))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 714752 128 c714752) (checkChunk_sound 714880 128 c714880)) (Checked.append (checkChunk_sound 715008 128 c715008) (checkChunk_sound 715136 128 c715136))) (Checked.append (Checked.append (checkChunk_sound 715264 128 c715264) (checkChunk_sound 715392 128 c715392)) (Checked.append (checkChunk_sound 715520 128 c715520) (checkChunk_sound 715648 128 c715648)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 715776 128 c715776) (checkChunk_sound 715904 128 c715904)) (Checked.append (checkChunk_sound 716032 128 c716032) (checkChunk_sound 716160 128 c716160))) (Checked.append (Checked.append (checkChunk_sound 716288 128 c716288) (checkChunk_sound 716416 128 c716416)) (Checked.append (checkChunk_sound 716544 128 c716544) (checkChunk_sound 716672 128 c716672)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 716800 128 c716800) (checkChunk_sound 716928 128 c716928)) (Checked.append (checkChunk_sound 717056 128 c717056) (checkChunk_sound 717184 128 c717184))) (Checked.append (Checked.append (checkChunk_sound 717312 128 c717312) (checkChunk_sound 717440 128 c717440)) (Checked.append (checkChunk_sound 717568 128 c717568) (checkChunk_sound 717696 128 c717696)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 717824 128 c717824) (checkChunk_sound 717952 128 c717952)) (Checked.append (checkChunk_sound 718080 128 c718080) (checkChunk_sound 718208 128 c718208))) (Checked.append (Checked.append (checkChunk_sound 718336 128 c718336) (checkChunk_sound 718464 128 c718464)) (Checked.append (checkChunk_sound 718592 128 c718592) (checkChunk_sound 718720 128 c718720))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 718848 128 c718848) (checkChunk_sound 718976 128 c718976)) (Checked.append (checkChunk_sound 719104 128 c719104) (checkChunk_sound 719232 128 c719232))) (Checked.append (Checked.append (checkChunk_sound 719360 128 c719360) (checkChunk_sound 719488 128 c719488)) (Checked.append (checkChunk_sound 719616 128 c719616) (checkChunk_sound 719744 128 c719744)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 719872 128 c719872) (checkChunk_sound 720000 128 c720000)) (Checked.append (checkChunk_sound 720128 128 c720128) (checkChunk_sound 720256 128 c720256))) (Checked.append (Checked.append (checkChunk_sound 720384 128 c720384) (checkChunk_sound 720512 128 c720512)) (Checked.append (checkChunk_sound 720640 128 c720640) (checkChunk_sound 720768 128 c720768)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B008
