module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [73728, 81920).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B008
private theorem c73728 : checkChunk 73728 128 = true := by decide +kernel
private theorem c73856 : checkChunk 73856 128 = true := by decide +kernel
private theorem c73984 : checkChunk 73984 128 = true := by decide +kernel
private theorem c74112 : checkChunk 74112 128 = true := by decide +kernel
private theorem c74240 : checkChunk 74240 128 = true := by decide +kernel
private theorem c74368 : checkChunk 74368 128 = true := by decide +kernel
private theorem c74496 : checkChunk 74496 128 = true := by decide +kernel
private theorem c74624 : checkChunk 74624 128 = true := by decide +kernel
private theorem c74752 : checkChunk 74752 128 = true := by decide +kernel
private theorem c74880 : checkChunk 74880 128 = true := by decide +kernel
private theorem c75008 : checkChunk 75008 128 = true := by decide +kernel
private theorem c75136 : checkChunk 75136 128 = true := by decide +kernel
private theorem c75264 : checkChunk 75264 128 = true := by decide +kernel
private theorem c75392 : checkChunk 75392 128 = true := by decide +kernel
private theorem c75520 : checkChunk 75520 128 = true := by decide +kernel
private theorem c75648 : checkChunk 75648 128 = true := by decide +kernel
private theorem c75776 : checkChunk 75776 128 = true := by decide +kernel
private theorem c75904 : checkChunk 75904 128 = true := by decide +kernel
private theorem c76032 : checkChunk 76032 128 = true := by decide +kernel
private theorem c76160 : checkChunk 76160 128 = true := by decide +kernel
private theorem c76288 : checkChunk 76288 128 = true := by decide +kernel
private theorem c76416 : checkChunk 76416 128 = true := by decide +kernel
private theorem c76544 : checkChunk 76544 128 = true := by decide +kernel
private theorem c76672 : checkChunk 76672 128 = true := by decide +kernel
private theorem c76800 : checkChunk 76800 128 = true := by decide +kernel
private theorem c76928 : checkChunk 76928 128 = true := by decide +kernel
private theorem c77056 : checkChunk 77056 128 = true := by decide +kernel
private theorem c77184 : checkChunk 77184 128 = true := by decide +kernel
private theorem c77312 : checkChunk 77312 128 = true := by decide +kernel
private theorem c77440 : checkChunk 77440 128 = true := by decide +kernel
private theorem c77568 : checkChunk 77568 128 = true := by decide +kernel
private theorem c77696 : checkChunk 77696 128 = true := by decide +kernel
private theorem c77824 : checkChunk 77824 128 = true := by decide +kernel
private theorem c77952 : checkChunk 77952 128 = true := by decide +kernel
private theorem c78080 : checkChunk 78080 128 = true := by decide +kernel
private theorem c78208 : checkChunk 78208 128 = true := by decide +kernel
private theorem c78336 : checkChunk 78336 128 = true := by decide +kernel
private theorem c78464 : checkChunk 78464 128 = true := by decide +kernel
private theorem c78592 : checkChunk 78592 128 = true := by decide +kernel
private theorem c78720 : checkChunk 78720 128 = true := by decide +kernel
private theorem c78848 : checkChunk 78848 128 = true := by decide +kernel
private theorem c78976 : checkChunk 78976 128 = true := by decide +kernel
private theorem c79104 : checkChunk 79104 128 = true := by decide +kernel
private theorem c79232 : checkChunk 79232 128 = true := by decide +kernel
private theorem c79360 : checkChunk 79360 128 = true := by decide +kernel
private theorem c79488 : checkChunk 79488 128 = true := by decide +kernel
private theorem c79616 : checkChunk 79616 128 = true := by decide +kernel
private theorem c79744 : checkChunk 79744 128 = true := by decide +kernel
private theorem c79872 : checkChunk 79872 128 = true := by decide +kernel
private theorem c80000 : checkChunk 80000 128 = true := by decide +kernel
private theorem c80128 : checkChunk 80128 128 = true := by decide +kernel
private theorem c80256 : checkChunk 80256 128 = true := by decide +kernel
private theorem c80384 : checkChunk 80384 128 = true := by decide +kernel
private theorem c80512 : checkChunk 80512 128 = true := by decide +kernel
private theorem c80640 : checkChunk 80640 128 = true := by decide +kernel
private theorem c80768 : checkChunk 80768 128 = true := by decide +kernel
private theorem c80896 : checkChunk 80896 128 = true := by decide +kernel
private theorem c81024 : checkChunk 81024 128 = true := by decide +kernel
private theorem c81152 : checkChunk 81152 128 = true := by decide +kernel
private theorem c81280 : checkChunk 81280 128 = true := by decide +kernel
private theorem c81408 : checkChunk 81408 128 = true := by decide +kernel
private theorem c81536 : checkChunk 81536 128 = true := by decide +kernel
private theorem c81664 : checkChunk 81664 128 = true := by decide +kernel
private theorem c81792 : checkChunk 81792 128 = true := by decide +kernel

public theorem checked : Checked 73728 81920 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 73728 128 c73728) (checkChunk_sound 73856 128 c73856)) (Checked.append (checkChunk_sound 73984 128 c73984) (checkChunk_sound 74112 128 c74112))) (Checked.append (Checked.append (checkChunk_sound 74240 128 c74240) (checkChunk_sound 74368 128 c74368)) (Checked.append (checkChunk_sound 74496 128 c74496) (checkChunk_sound 74624 128 c74624)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 74752 128 c74752) (checkChunk_sound 74880 128 c74880)) (Checked.append (checkChunk_sound 75008 128 c75008) (checkChunk_sound 75136 128 c75136))) (Checked.append (Checked.append (checkChunk_sound 75264 128 c75264) (checkChunk_sound 75392 128 c75392)) (Checked.append (checkChunk_sound 75520 128 c75520) (checkChunk_sound 75648 128 c75648))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 75776 128 c75776) (checkChunk_sound 75904 128 c75904)) (Checked.append (checkChunk_sound 76032 128 c76032) (checkChunk_sound 76160 128 c76160))) (Checked.append (Checked.append (checkChunk_sound 76288 128 c76288) (checkChunk_sound 76416 128 c76416)) (Checked.append (checkChunk_sound 76544 128 c76544) (checkChunk_sound 76672 128 c76672)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 76800 128 c76800) (checkChunk_sound 76928 128 c76928)) (Checked.append (checkChunk_sound 77056 128 c77056) (checkChunk_sound 77184 128 c77184))) (Checked.append (Checked.append (checkChunk_sound 77312 128 c77312) (checkChunk_sound 77440 128 c77440)) (Checked.append (checkChunk_sound 77568 128 c77568) (checkChunk_sound 77696 128 c77696)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 77824 128 c77824) (checkChunk_sound 77952 128 c77952)) (Checked.append (checkChunk_sound 78080 128 c78080) (checkChunk_sound 78208 128 c78208))) (Checked.append (Checked.append (checkChunk_sound 78336 128 c78336) (checkChunk_sound 78464 128 c78464)) (Checked.append (checkChunk_sound 78592 128 c78592) (checkChunk_sound 78720 128 c78720)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 78848 128 c78848) (checkChunk_sound 78976 128 c78976)) (Checked.append (checkChunk_sound 79104 128 c79104) (checkChunk_sound 79232 128 c79232))) (Checked.append (Checked.append (checkChunk_sound 79360 128 c79360) (checkChunk_sound 79488 128 c79488)) (Checked.append (checkChunk_sound 79616 128 c79616) (checkChunk_sound 79744 128 c79744))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 79872 128 c79872) (checkChunk_sound 80000 128 c80000)) (Checked.append (checkChunk_sound 80128 128 c80128) (checkChunk_sound 80256 128 c80256))) (Checked.append (Checked.append (checkChunk_sound 80384 128 c80384) (checkChunk_sound 80512 128 c80512)) (Checked.append (checkChunk_sound 80640 128 c80640) (checkChunk_sound 80768 128 c80768)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 80896 128 c80896) (checkChunk_sound 81024 128 c81024)) (Checked.append (checkChunk_sound 81152 128 c81152) (checkChunk_sound 81280 128 c81280))) (Checked.append (Checked.append (checkChunk_sound 81408 128 c81408) (checkChunk_sound 81536 128 c81536)) (Checked.append (checkChunk_sound 81664 128 c81664) (checkChunk_sound 81792 128 c81792)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B008
