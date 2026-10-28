module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1064960, 1073152).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B025
private theorem c1064960 : checkChunk 1064960 128 = true := by decide +kernel
private theorem c1065088 : checkChunk 1065088 128 = true := by decide +kernel
private theorem c1065216 : checkChunk 1065216 128 = true := by decide +kernel
private theorem c1065344 : checkChunk 1065344 128 = true := by decide +kernel
private theorem c1065472 : checkChunk 1065472 128 = true := by decide +kernel
private theorem c1065600 : checkChunk 1065600 128 = true := by decide +kernel
private theorem c1065728 : checkChunk 1065728 128 = true := by decide +kernel
private theorem c1065856 : checkChunk 1065856 128 = true := by decide +kernel
private theorem c1065984 : checkChunk 1065984 128 = true := by decide +kernel
private theorem c1066112 : checkChunk 1066112 128 = true := by decide +kernel
private theorem c1066240 : checkChunk 1066240 128 = true := by decide +kernel
private theorem c1066368 : checkChunk 1066368 128 = true := by decide +kernel
private theorem c1066496 : checkChunk 1066496 128 = true := by decide +kernel
private theorem c1066624 : checkChunk 1066624 128 = true := by decide +kernel
private theorem c1066752 : checkChunk 1066752 128 = true := by decide +kernel
private theorem c1066880 : checkChunk 1066880 128 = true := by decide +kernel
private theorem c1067008 : checkChunk 1067008 128 = true := by decide +kernel
private theorem c1067136 : checkChunk 1067136 128 = true := by decide +kernel
private theorem c1067264 : checkChunk 1067264 128 = true := by decide +kernel
private theorem c1067392 : checkChunk 1067392 128 = true := by decide +kernel
private theorem c1067520 : checkChunk 1067520 128 = true := by decide +kernel
private theorem c1067648 : checkChunk 1067648 128 = true := by decide +kernel
private theorem c1067776 : checkChunk 1067776 128 = true := by decide +kernel
private theorem c1067904 : checkChunk 1067904 128 = true := by decide +kernel
private theorem c1068032 : checkChunk 1068032 128 = true := by decide +kernel
private theorem c1068160 : checkChunk 1068160 128 = true := by decide +kernel
private theorem c1068288 : checkChunk 1068288 128 = true := by decide +kernel
private theorem c1068416 : checkChunk 1068416 128 = true := by decide +kernel
private theorem c1068544 : checkChunk 1068544 128 = true := by decide +kernel
private theorem c1068672 : checkChunk 1068672 128 = true := by decide +kernel
private theorem c1068800 : checkChunk 1068800 128 = true := by decide +kernel
private theorem c1068928 : checkChunk 1068928 128 = true := by decide +kernel
private theorem c1069056 : checkChunk 1069056 128 = true := by decide +kernel
private theorem c1069184 : checkChunk 1069184 128 = true := by decide +kernel
private theorem c1069312 : checkChunk 1069312 128 = true := by decide +kernel
private theorem c1069440 : checkChunk 1069440 128 = true := by decide +kernel
private theorem c1069568 : checkChunk 1069568 128 = true := by decide +kernel
private theorem c1069696 : checkChunk 1069696 128 = true := by decide +kernel
private theorem c1069824 : checkChunk 1069824 128 = true := by decide +kernel
private theorem c1069952 : checkChunk 1069952 128 = true := by decide +kernel
private theorem c1070080 : checkChunk 1070080 128 = true := by decide +kernel
private theorem c1070208 : checkChunk 1070208 128 = true := by decide +kernel
private theorem c1070336 : checkChunk 1070336 128 = true := by decide +kernel
private theorem c1070464 : checkChunk 1070464 128 = true := by decide +kernel
private theorem c1070592 : checkChunk 1070592 128 = true := by decide +kernel
private theorem c1070720 : checkChunk 1070720 128 = true := by decide +kernel
private theorem c1070848 : checkChunk 1070848 128 = true := by decide +kernel
private theorem c1070976 : checkChunk 1070976 128 = true := by decide +kernel
private theorem c1071104 : checkChunk 1071104 128 = true := by decide +kernel
private theorem c1071232 : checkChunk 1071232 128 = true := by decide +kernel
private theorem c1071360 : checkChunk 1071360 128 = true := by decide +kernel
private theorem c1071488 : checkChunk 1071488 128 = true := by decide +kernel
private theorem c1071616 : checkChunk 1071616 128 = true := by decide +kernel
private theorem c1071744 : checkChunk 1071744 128 = true := by decide +kernel
private theorem c1071872 : checkChunk 1071872 128 = true := by decide +kernel
private theorem c1072000 : checkChunk 1072000 128 = true := by decide +kernel
private theorem c1072128 : checkChunk 1072128 128 = true := by decide +kernel
private theorem c1072256 : checkChunk 1072256 128 = true := by decide +kernel
private theorem c1072384 : checkChunk 1072384 128 = true := by decide +kernel
private theorem c1072512 : checkChunk 1072512 128 = true := by decide +kernel
private theorem c1072640 : checkChunk 1072640 128 = true := by decide +kernel
private theorem c1072768 : checkChunk 1072768 128 = true := by decide +kernel
private theorem c1072896 : checkChunk 1072896 128 = true := by decide +kernel
private theorem c1073024 : checkChunk 1073024 128 = true := by decide +kernel

public theorem checked : Checked 1064960 1073152 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1064960 128 c1064960) (checkChunk_sound 1065088 128 c1065088)) (Checked.append (checkChunk_sound 1065216 128 c1065216) (checkChunk_sound 1065344 128 c1065344))) (Checked.append (Checked.append (checkChunk_sound 1065472 128 c1065472) (checkChunk_sound 1065600 128 c1065600)) (Checked.append (checkChunk_sound 1065728 128 c1065728) (checkChunk_sound 1065856 128 c1065856)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1065984 128 c1065984) (checkChunk_sound 1066112 128 c1066112)) (Checked.append (checkChunk_sound 1066240 128 c1066240) (checkChunk_sound 1066368 128 c1066368))) (Checked.append (Checked.append (checkChunk_sound 1066496 128 c1066496) (checkChunk_sound 1066624 128 c1066624)) (Checked.append (checkChunk_sound 1066752 128 c1066752) (checkChunk_sound 1066880 128 c1066880))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1067008 128 c1067008) (checkChunk_sound 1067136 128 c1067136)) (Checked.append (checkChunk_sound 1067264 128 c1067264) (checkChunk_sound 1067392 128 c1067392))) (Checked.append (Checked.append (checkChunk_sound 1067520 128 c1067520) (checkChunk_sound 1067648 128 c1067648)) (Checked.append (checkChunk_sound 1067776 128 c1067776) (checkChunk_sound 1067904 128 c1067904)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1068032 128 c1068032) (checkChunk_sound 1068160 128 c1068160)) (Checked.append (checkChunk_sound 1068288 128 c1068288) (checkChunk_sound 1068416 128 c1068416))) (Checked.append (Checked.append (checkChunk_sound 1068544 128 c1068544) (checkChunk_sound 1068672 128 c1068672)) (Checked.append (checkChunk_sound 1068800 128 c1068800) (checkChunk_sound 1068928 128 c1068928)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1069056 128 c1069056) (checkChunk_sound 1069184 128 c1069184)) (Checked.append (checkChunk_sound 1069312 128 c1069312) (checkChunk_sound 1069440 128 c1069440))) (Checked.append (Checked.append (checkChunk_sound 1069568 128 c1069568) (checkChunk_sound 1069696 128 c1069696)) (Checked.append (checkChunk_sound 1069824 128 c1069824) (checkChunk_sound 1069952 128 c1069952)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1070080 128 c1070080) (checkChunk_sound 1070208 128 c1070208)) (Checked.append (checkChunk_sound 1070336 128 c1070336) (checkChunk_sound 1070464 128 c1070464))) (Checked.append (Checked.append (checkChunk_sound 1070592 128 c1070592) (checkChunk_sound 1070720 128 c1070720)) (Checked.append (checkChunk_sound 1070848 128 c1070848) (checkChunk_sound 1070976 128 c1070976))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1071104 128 c1071104) (checkChunk_sound 1071232 128 c1071232)) (Checked.append (checkChunk_sound 1071360 128 c1071360) (checkChunk_sound 1071488 128 c1071488))) (Checked.append (Checked.append (checkChunk_sound 1071616 128 c1071616) (checkChunk_sound 1071744 128 c1071744)) (Checked.append (checkChunk_sound 1071872 128 c1071872) (checkChunk_sound 1072000 128 c1072000)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1072128 128 c1072128) (checkChunk_sound 1072256 128 c1072256)) (Checked.append (checkChunk_sound 1072384 128 c1072384) (checkChunk_sound 1072512 128 c1072512))) (Checked.append (Checked.append (checkChunk_sound 1072640 128 c1072640) (checkChunk_sound 1072768 128 c1072768)) (Checked.append (checkChunk_sound 1072896 128 c1072896) (checkChunk_sound 1073024 128 c1073024)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B025
