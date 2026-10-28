module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1163264, 1171456).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B011
private theorem c1163264 : checkChunk 1163264 128 = true := by decide +kernel
private theorem c1163392 : checkChunk 1163392 128 = true := by decide +kernel
private theorem c1163520 : checkChunk 1163520 128 = true := by decide +kernel
private theorem c1163648 : checkChunk 1163648 128 = true := by decide +kernel
private theorem c1163776 : checkChunk 1163776 128 = true := by decide +kernel
private theorem c1163904 : checkChunk 1163904 128 = true := by decide +kernel
private theorem c1164032 : checkChunk 1164032 128 = true := by decide +kernel
private theorem c1164160 : checkChunk 1164160 128 = true := by decide +kernel
private theorem c1164288 : checkChunk 1164288 128 = true := by decide +kernel
private theorem c1164416 : checkChunk 1164416 128 = true := by decide +kernel
private theorem c1164544 : checkChunk 1164544 128 = true := by decide +kernel
private theorem c1164672 : checkChunk 1164672 128 = true := by decide +kernel
private theorem c1164800 : checkChunk 1164800 128 = true := by decide +kernel
private theorem c1164928 : checkChunk 1164928 128 = true := by decide +kernel
private theorem c1165056 : checkChunk 1165056 128 = true := by decide +kernel
private theorem c1165184 : checkChunk 1165184 128 = true := by decide +kernel
private theorem c1165312 : checkChunk 1165312 128 = true := by decide +kernel
private theorem c1165440 : checkChunk 1165440 128 = true := by decide +kernel
private theorem c1165568 : checkChunk 1165568 128 = true := by decide +kernel
private theorem c1165696 : checkChunk 1165696 128 = true := by decide +kernel
private theorem c1165824 : checkChunk 1165824 128 = true := by decide +kernel
private theorem c1165952 : checkChunk 1165952 128 = true := by decide +kernel
private theorem c1166080 : checkChunk 1166080 128 = true := by decide +kernel
private theorem c1166208 : checkChunk 1166208 128 = true := by decide +kernel
private theorem c1166336 : checkChunk 1166336 128 = true := by decide +kernel
private theorem c1166464 : checkChunk 1166464 128 = true := by decide +kernel
private theorem c1166592 : checkChunk 1166592 128 = true := by decide +kernel
private theorem c1166720 : checkChunk 1166720 128 = true := by decide +kernel
private theorem c1166848 : checkChunk 1166848 128 = true := by decide +kernel
private theorem c1166976 : checkChunk 1166976 128 = true := by decide +kernel
private theorem c1167104 : checkChunk 1167104 128 = true := by decide +kernel
private theorem c1167232 : checkChunk 1167232 128 = true := by decide +kernel
private theorem c1167360 : checkChunk 1167360 128 = true := by decide +kernel
private theorem c1167488 : checkChunk 1167488 128 = true := by decide +kernel
private theorem c1167616 : checkChunk 1167616 128 = true := by decide +kernel
private theorem c1167744 : checkChunk 1167744 128 = true := by decide +kernel
private theorem c1167872 : checkChunk 1167872 128 = true := by decide +kernel
private theorem c1168000 : checkChunk 1168000 128 = true := by decide +kernel
private theorem c1168128 : checkChunk 1168128 128 = true := by decide +kernel
private theorem c1168256 : checkChunk 1168256 128 = true := by decide +kernel
private theorem c1168384 : checkChunk 1168384 128 = true := by decide +kernel
private theorem c1168512 : checkChunk 1168512 128 = true := by decide +kernel
private theorem c1168640 : checkChunk 1168640 128 = true := by decide +kernel
private theorem c1168768 : checkChunk 1168768 128 = true := by decide +kernel
private theorem c1168896 : checkChunk 1168896 128 = true := by decide +kernel
private theorem c1169024 : checkChunk 1169024 128 = true := by decide +kernel
private theorem c1169152 : checkChunk 1169152 128 = true := by decide +kernel
private theorem c1169280 : checkChunk 1169280 128 = true := by decide +kernel
private theorem c1169408 : checkChunk 1169408 128 = true := by decide +kernel
private theorem c1169536 : checkChunk 1169536 128 = true := by decide +kernel
private theorem c1169664 : checkChunk 1169664 128 = true := by decide +kernel
private theorem c1169792 : checkChunk 1169792 128 = true := by decide +kernel
private theorem c1169920 : checkChunk 1169920 128 = true := by decide +kernel
private theorem c1170048 : checkChunk 1170048 128 = true := by decide +kernel
private theorem c1170176 : checkChunk 1170176 128 = true := by decide +kernel
private theorem c1170304 : checkChunk 1170304 128 = true := by decide +kernel
private theorem c1170432 : checkChunk 1170432 128 = true := by decide +kernel
private theorem c1170560 : checkChunk 1170560 128 = true := by decide +kernel
private theorem c1170688 : checkChunk 1170688 128 = true := by decide +kernel
private theorem c1170816 : checkChunk 1170816 128 = true := by decide +kernel
private theorem c1170944 : checkChunk 1170944 128 = true := by decide +kernel
private theorem c1171072 : checkChunk 1171072 128 = true := by decide +kernel
private theorem c1171200 : checkChunk 1171200 128 = true := by decide +kernel
private theorem c1171328 : checkChunk 1171328 128 = true := by decide +kernel

public theorem checked : Checked 1163264 1171456 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1163264 128 c1163264) (checkChunk_sound 1163392 128 c1163392)) (Checked.append (checkChunk_sound 1163520 128 c1163520) (checkChunk_sound 1163648 128 c1163648))) (Checked.append (Checked.append (checkChunk_sound 1163776 128 c1163776) (checkChunk_sound 1163904 128 c1163904)) (Checked.append (checkChunk_sound 1164032 128 c1164032) (checkChunk_sound 1164160 128 c1164160)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1164288 128 c1164288) (checkChunk_sound 1164416 128 c1164416)) (Checked.append (checkChunk_sound 1164544 128 c1164544) (checkChunk_sound 1164672 128 c1164672))) (Checked.append (Checked.append (checkChunk_sound 1164800 128 c1164800) (checkChunk_sound 1164928 128 c1164928)) (Checked.append (checkChunk_sound 1165056 128 c1165056) (checkChunk_sound 1165184 128 c1165184))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1165312 128 c1165312) (checkChunk_sound 1165440 128 c1165440)) (Checked.append (checkChunk_sound 1165568 128 c1165568) (checkChunk_sound 1165696 128 c1165696))) (Checked.append (Checked.append (checkChunk_sound 1165824 128 c1165824) (checkChunk_sound 1165952 128 c1165952)) (Checked.append (checkChunk_sound 1166080 128 c1166080) (checkChunk_sound 1166208 128 c1166208)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1166336 128 c1166336) (checkChunk_sound 1166464 128 c1166464)) (Checked.append (checkChunk_sound 1166592 128 c1166592) (checkChunk_sound 1166720 128 c1166720))) (Checked.append (Checked.append (checkChunk_sound 1166848 128 c1166848) (checkChunk_sound 1166976 128 c1166976)) (Checked.append (checkChunk_sound 1167104 128 c1167104) (checkChunk_sound 1167232 128 c1167232)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1167360 128 c1167360) (checkChunk_sound 1167488 128 c1167488)) (Checked.append (checkChunk_sound 1167616 128 c1167616) (checkChunk_sound 1167744 128 c1167744))) (Checked.append (Checked.append (checkChunk_sound 1167872 128 c1167872) (checkChunk_sound 1168000 128 c1168000)) (Checked.append (checkChunk_sound 1168128 128 c1168128) (checkChunk_sound 1168256 128 c1168256)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1168384 128 c1168384) (checkChunk_sound 1168512 128 c1168512)) (Checked.append (checkChunk_sound 1168640 128 c1168640) (checkChunk_sound 1168768 128 c1168768))) (Checked.append (Checked.append (checkChunk_sound 1168896 128 c1168896) (checkChunk_sound 1169024 128 c1169024)) (Checked.append (checkChunk_sound 1169152 128 c1169152) (checkChunk_sound 1169280 128 c1169280))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1169408 128 c1169408) (checkChunk_sound 1169536 128 c1169536)) (Checked.append (checkChunk_sound 1169664 128 c1169664) (checkChunk_sound 1169792 128 c1169792))) (Checked.append (Checked.append (checkChunk_sound 1169920 128 c1169920) (checkChunk_sound 1170048 128 c1170048)) (Checked.append (checkChunk_sound 1170176 128 c1170176) (checkChunk_sound 1170304 128 c1170304)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1170432 128 c1170432) (checkChunk_sound 1170560 128 c1170560)) (Checked.append (checkChunk_sound 1170688 128 c1170688) (checkChunk_sound 1170816 128 c1170816))) (Checked.append (Checked.append (checkChunk_sound 1170944 128 c1170944) (checkChunk_sound 1171072 128 c1171072)) (Checked.append (checkChunk_sound 1171200 128 c1171200) (checkChunk_sound 1171328 128 c1171328)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B011
