module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1097728, 1105920).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B003
private theorem c1097728 : checkChunk 1097728 128 = true := by decide +kernel
private theorem c1097856 : checkChunk 1097856 128 = true := by decide +kernel
private theorem c1097984 : checkChunk 1097984 128 = true := by decide +kernel
private theorem c1098112 : checkChunk 1098112 128 = true := by decide +kernel
private theorem c1098240 : checkChunk 1098240 128 = true := by decide +kernel
private theorem c1098368 : checkChunk 1098368 128 = true := by decide +kernel
private theorem c1098496 : checkChunk 1098496 128 = true := by decide +kernel
private theorem c1098624 : checkChunk 1098624 128 = true := by decide +kernel
private theorem c1098752 : checkChunk 1098752 128 = true := by decide +kernel
private theorem c1098880 : checkChunk 1098880 128 = true := by decide +kernel
private theorem c1099008 : checkChunk 1099008 128 = true := by decide +kernel
private theorem c1099136 : checkChunk 1099136 128 = true := by decide +kernel
private theorem c1099264 : checkChunk 1099264 128 = true := by decide +kernel
private theorem c1099392 : checkChunk 1099392 128 = true := by decide +kernel
private theorem c1099520 : checkChunk 1099520 128 = true := by decide +kernel
private theorem c1099648 : checkChunk 1099648 128 = true := by decide +kernel
private theorem c1099776 : checkChunk 1099776 128 = true := by decide +kernel
private theorem c1099904 : checkChunk 1099904 128 = true := by decide +kernel
private theorem c1100032 : checkChunk 1100032 128 = true := by decide +kernel
private theorem c1100160 : checkChunk 1100160 128 = true := by decide +kernel
private theorem c1100288 : checkChunk 1100288 128 = true := by decide +kernel
private theorem c1100416 : checkChunk 1100416 128 = true := by decide +kernel
private theorem c1100544 : checkChunk 1100544 128 = true := by decide +kernel
private theorem c1100672 : checkChunk 1100672 128 = true := by decide +kernel
private theorem c1100800 : checkChunk 1100800 128 = true := by decide +kernel
private theorem c1100928 : checkChunk 1100928 128 = true := by decide +kernel
private theorem c1101056 : checkChunk 1101056 128 = true := by decide +kernel
private theorem c1101184 : checkChunk 1101184 128 = true := by decide +kernel
private theorem c1101312 : checkChunk 1101312 128 = true := by decide +kernel
private theorem c1101440 : checkChunk 1101440 128 = true := by decide +kernel
private theorem c1101568 : checkChunk 1101568 128 = true := by decide +kernel
private theorem c1101696 : checkChunk 1101696 128 = true := by decide +kernel
private theorem c1101824 : checkChunk 1101824 128 = true := by decide +kernel
private theorem c1101952 : checkChunk 1101952 128 = true := by decide +kernel
private theorem c1102080 : checkChunk 1102080 128 = true := by decide +kernel
private theorem c1102208 : checkChunk 1102208 128 = true := by decide +kernel
private theorem c1102336 : checkChunk 1102336 128 = true := by decide +kernel
private theorem c1102464 : checkChunk 1102464 128 = true := by decide +kernel
private theorem c1102592 : checkChunk 1102592 128 = true := by decide +kernel
private theorem c1102720 : checkChunk 1102720 128 = true := by decide +kernel
private theorem c1102848 : checkChunk 1102848 128 = true := by decide +kernel
private theorem c1102976 : checkChunk 1102976 128 = true := by decide +kernel
private theorem c1103104 : checkChunk 1103104 128 = true := by decide +kernel
private theorem c1103232 : checkChunk 1103232 128 = true := by decide +kernel
private theorem c1103360 : checkChunk 1103360 128 = true := by decide +kernel
private theorem c1103488 : checkChunk 1103488 128 = true := by decide +kernel
private theorem c1103616 : checkChunk 1103616 128 = true := by decide +kernel
private theorem c1103744 : checkChunk 1103744 128 = true := by decide +kernel
private theorem c1103872 : checkChunk 1103872 128 = true := by decide +kernel
private theorem c1104000 : checkChunk 1104000 128 = true := by decide +kernel
private theorem c1104128 : checkChunk 1104128 128 = true := by decide +kernel
private theorem c1104256 : checkChunk 1104256 128 = true := by decide +kernel
private theorem c1104384 : checkChunk 1104384 128 = true := by decide +kernel
private theorem c1104512 : checkChunk 1104512 128 = true := by decide +kernel
private theorem c1104640 : checkChunk 1104640 128 = true := by decide +kernel
private theorem c1104768 : checkChunk 1104768 128 = true := by decide +kernel
private theorem c1104896 : checkChunk 1104896 128 = true := by decide +kernel
private theorem c1105024 : checkChunk 1105024 128 = true := by decide +kernel
private theorem c1105152 : checkChunk 1105152 128 = true := by decide +kernel
private theorem c1105280 : checkChunk 1105280 128 = true := by decide +kernel
private theorem c1105408 : checkChunk 1105408 128 = true := by decide +kernel
private theorem c1105536 : checkChunk 1105536 128 = true := by decide +kernel
private theorem c1105664 : checkChunk 1105664 128 = true := by decide +kernel
private theorem c1105792 : checkChunk 1105792 128 = true := by decide +kernel

public theorem checked : Checked 1097728 1105920 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1097728 128 c1097728) (checkChunk_sound 1097856 128 c1097856)) (Checked.append (checkChunk_sound 1097984 128 c1097984) (checkChunk_sound 1098112 128 c1098112))) (Checked.append (Checked.append (checkChunk_sound 1098240 128 c1098240) (checkChunk_sound 1098368 128 c1098368)) (Checked.append (checkChunk_sound 1098496 128 c1098496) (checkChunk_sound 1098624 128 c1098624)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1098752 128 c1098752) (checkChunk_sound 1098880 128 c1098880)) (Checked.append (checkChunk_sound 1099008 128 c1099008) (checkChunk_sound 1099136 128 c1099136))) (Checked.append (Checked.append (checkChunk_sound 1099264 128 c1099264) (checkChunk_sound 1099392 128 c1099392)) (Checked.append (checkChunk_sound 1099520 128 c1099520) (checkChunk_sound 1099648 128 c1099648))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1099776 128 c1099776) (checkChunk_sound 1099904 128 c1099904)) (Checked.append (checkChunk_sound 1100032 128 c1100032) (checkChunk_sound 1100160 128 c1100160))) (Checked.append (Checked.append (checkChunk_sound 1100288 128 c1100288) (checkChunk_sound 1100416 128 c1100416)) (Checked.append (checkChunk_sound 1100544 128 c1100544) (checkChunk_sound 1100672 128 c1100672)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1100800 128 c1100800) (checkChunk_sound 1100928 128 c1100928)) (Checked.append (checkChunk_sound 1101056 128 c1101056) (checkChunk_sound 1101184 128 c1101184))) (Checked.append (Checked.append (checkChunk_sound 1101312 128 c1101312) (checkChunk_sound 1101440 128 c1101440)) (Checked.append (checkChunk_sound 1101568 128 c1101568) (checkChunk_sound 1101696 128 c1101696)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1101824 128 c1101824) (checkChunk_sound 1101952 128 c1101952)) (Checked.append (checkChunk_sound 1102080 128 c1102080) (checkChunk_sound 1102208 128 c1102208))) (Checked.append (Checked.append (checkChunk_sound 1102336 128 c1102336) (checkChunk_sound 1102464 128 c1102464)) (Checked.append (checkChunk_sound 1102592 128 c1102592) (checkChunk_sound 1102720 128 c1102720)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1102848 128 c1102848) (checkChunk_sound 1102976 128 c1102976)) (Checked.append (checkChunk_sound 1103104 128 c1103104) (checkChunk_sound 1103232 128 c1103232))) (Checked.append (Checked.append (checkChunk_sound 1103360 128 c1103360) (checkChunk_sound 1103488 128 c1103488)) (Checked.append (checkChunk_sound 1103616 128 c1103616) (checkChunk_sound 1103744 128 c1103744))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1103872 128 c1103872) (checkChunk_sound 1104000 128 c1104000)) (Checked.append (checkChunk_sound 1104128 128 c1104128) (checkChunk_sound 1104256 128 c1104256))) (Checked.append (Checked.append (checkChunk_sound 1104384 128 c1104384) (checkChunk_sound 1104512 128 c1104512)) (Checked.append (checkChunk_sound 1104640 128 c1104640) (checkChunk_sound 1104768 128 c1104768)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1104896 128 c1104896) (checkChunk_sound 1105024 128 c1105024)) (Checked.append (checkChunk_sound 1105152 128 c1105152) (checkChunk_sound 1105280 128 c1105280))) (Checked.append (Checked.append (checkChunk_sound 1105408 128 c1105408) (checkChunk_sound 1105536 128 c1105536)) (Checked.append (checkChunk_sound 1105664 128 c1105664) (checkChunk_sound 1105792 128 c1105792)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B003
