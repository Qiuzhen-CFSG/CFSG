module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1269760, 1277952).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B024
private theorem c1269760 : checkChunk 1269760 128 = true := by decide +kernel
private theorem c1269888 : checkChunk 1269888 128 = true := by decide +kernel
private theorem c1270016 : checkChunk 1270016 128 = true := by decide +kernel
private theorem c1270144 : checkChunk 1270144 128 = true := by decide +kernel
private theorem c1270272 : checkChunk 1270272 128 = true := by decide +kernel
private theorem c1270400 : checkChunk 1270400 128 = true := by decide +kernel
private theorem c1270528 : checkChunk 1270528 128 = true := by decide +kernel
private theorem c1270656 : checkChunk 1270656 128 = true := by decide +kernel
private theorem c1270784 : checkChunk 1270784 128 = true := by decide +kernel
private theorem c1270912 : checkChunk 1270912 128 = true := by decide +kernel
private theorem c1271040 : checkChunk 1271040 128 = true := by decide +kernel
private theorem c1271168 : checkChunk 1271168 128 = true := by decide +kernel
private theorem c1271296 : checkChunk 1271296 128 = true := by decide +kernel
private theorem c1271424 : checkChunk 1271424 128 = true := by decide +kernel
private theorem c1271552 : checkChunk 1271552 128 = true := by decide +kernel
private theorem c1271680 : checkChunk 1271680 128 = true := by decide +kernel
private theorem c1271808 : checkChunk 1271808 128 = true := by decide +kernel
private theorem c1271936 : checkChunk 1271936 128 = true := by decide +kernel
private theorem c1272064 : checkChunk 1272064 128 = true := by decide +kernel
private theorem c1272192 : checkChunk 1272192 128 = true := by decide +kernel
private theorem c1272320 : checkChunk 1272320 128 = true := by decide +kernel
private theorem c1272448 : checkChunk 1272448 128 = true := by decide +kernel
private theorem c1272576 : checkChunk 1272576 128 = true := by decide +kernel
private theorem c1272704 : checkChunk 1272704 128 = true := by decide +kernel
private theorem c1272832 : checkChunk 1272832 128 = true := by decide +kernel
private theorem c1272960 : checkChunk 1272960 128 = true := by decide +kernel
private theorem c1273088 : checkChunk 1273088 128 = true := by decide +kernel
private theorem c1273216 : checkChunk 1273216 128 = true := by decide +kernel
private theorem c1273344 : checkChunk 1273344 128 = true := by decide +kernel
private theorem c1273472 : checkChunk 1273472 128 = true := by decide +kernel
private theorem c1273600 : checkChunk 1273600 128 = true := by decide +kernel
private theorem c1273728 : checkChunk 1273728 128 = true := by decide +kernel
private theorem c1273856 : checkChunk 1273856 128 = true := by decide +kernel
private theorem c1273984 : checkChunk 1273984 128 = true := by decide +kernel
private theorem c1274112 : checkChunk 1274112 128 = true := by decide +kernel
private theorem c1274240 : checkChunk 1274240 128 = true := by decide +kernel
private theorem c1274368 : checkChunk 1274368 128 = true := by decide +kernel
private theorem c1274496 : checkChunk 1274496 128 = true := by decide +kernel
private theorem c1274624 : checkChunk 1274624 128 = true := by decide +kernel
private theorem c1274752 : checkChunk 1274752 128 = true := by decide +kernel
private theorem c1274880 : checkChunk 1274880 128 = true := by decide +kernel
private theorem c1275008 : checkChunk 1275008 128 = true := by decide +kernel
private theorem c1275136 : checkChunk 1275136 128 = true := by decide +kernel
private theorem c1275264 : checkChunk 1275264 128 = true := by decide +kernel
private theorem c1275392 : checkChunk 1275392 128 = true := by decide +kernel
private theorem c1275520 : checkChunk 1275520 128 = true := by decide +kernel
private theorem c1275648 : checkChunk 1275648 128 = true := by decide +kernel
private theorem c1275776 : checkChunk 1275776 128 = true := by decide +kernel
private theorem c1275904 : checkChunk 1275904 128 = true := by decide +kernel
private theorem c1276032 : checkChunk 1276032 128 = true := by decide +kernel
private theorem c1276160 : checkChunk 1276160 128 = true := by decide +kernel
private theorem c1276288 : checkChunk 1276288 128 = true := by decide +kernel
private theorem c1276416 : checkChunk 1276416 128 = true := by decide +kernel
private theorem c1276544 : checkChunk 1276544 128 = true := by decide +kernel
private theorem c1276672 : checkChunk 1276672 128 = true := by decide +kernel
private theorem c1276800 : checkChunk 1276800 128 = true := by decide +kernel
private theorem c1276928 : checkChunk 1276928 128 = true := by decide +kernel
private theorem c1277056 : checkChunk 1277056 128 = true := by decide +kernel
private theorem c1277184 : checkChunk 1277184 128 = true := by decide +kernel
private theorem c1277312 : checkChunk 1277312 128 = true := by decide +kernel
private theorem c1277440 : checkChunk 1277440 128 = true := by decide +kernel
private theorem c1277568 : checkChunk 1277568 128 = true := by decide +kernel
private theorem c1277696 : checkChunk 1277696 128 = true := by decide +kernel
private theorem c1277824 : checkChunk 1277824 128 = true := by decide +kernel

public theorem checked : Checked 1269760 1277952 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1269760 128 c1269760) (checkChunk_sound 1269888 128 c1269888)) (Checked.append (checkChunk_sound 1270016 128 c1270016) (checkChunk_sound 1270144 128 c1270144))) (Checked.append (Checked.append (checkChunk_sound 1270272 128 c1270272) (checkChunk_sound 1270400 128 c1270400)) (Checked.append (checkChunk_sound 1270528 128 c1270528) (checkChunk_sound 1270656 128 c1270656)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1270784 128 c1270784) (checkChunk_sound 1270912 128 c1270912)) (Checked.append (checkChunk_sound 1271040 128 c1271040) (checkChunk_sound 1271168 128 c1271168))) (Checked.append (Checked.append (checkChunk_sound 1271296 128 c1271296) (checkChunk_sound 1271424 128 c1271424)) (Checked.append (checkChunk_sound 1271552 128 c1271552) (checkChunk_sound 1271680 128 c1271680))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1271808 128 c1271808) (checkChunk_sound 1271936 128 c1271936)) (Checked.append (checkChunk_sound 1272064 128 c1272064) (checkChunk_sound 1272192 128 c1272192))) (Checked.append (Checked.append (checkChunk_sound 1272320 128 c1272320) (checkChunk_sound 1272448 128 c1272448)) (Checked.append (checkChunk_sound 1272576 128 c1272576) (checkChunk_sound 1272704 128 c1272704)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1272832 128 c1272832) (checkChunk_sound 1272960 128 c1272960)) (Checked.append (checkChunk_sound 1273088 128 c1273088) (checkChunk_sound 1273216 128 c1273216))) (Checked.append (Checked.append (checkChunk_sound 1273344 128 c1273344) (checkChunk_sound 1273472 128 c1273472)) (Checked.append (checkChunk_sound 1273600 128 c1273600) (checkChunk_sound 1273728 128 c1273728)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1273856 128 c1273856) (checkChunk_sound 1273984 128 c1273984)) (Checked.append (checkChunk_sound 1274112 128 c1274112) (checkChunk_sound 1274240 128 c1274240))) (Checked.append (Checked.append (checkChunk_sound 1274368 128 c1274368) (checkChunk_sound 1274496 128 c1274496)) (Checked.append (checkChunk_sound 1274624 128 c1274624) (checkChunk_sound 1274752 128 c1274752)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1274880 128 c1274880) (checkChunk_sound 1275008 128 c1275008)) (Checked.append (checkChunk_sound 1275136 128 c1275136) (checkChunk_sound 1275264 128 c1275264))) (Checked.append (Checked.append (checkChunk_sound 1275392 128 c1275392) (checkChunk_sound 1275520 128 c1275520)) (Checked.append (checkChunk_sound 1275648 128 c1275648) (checkChunk_sound 1275776 128 c1275776))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1275904 128 c1275904) (checkChunk_sound 1276032 128 c1276032)) (Checked.append (checkChunk_sound 1276160 128 c1276160) (checkChunk_sound 1276288 128 c1276288))) (Checked.append (Checked.append (checkChunk_sound 1276416 128 c1276416) (checkChunk_sound 1276544 128 c1276544)) (Checked.append (checkChunk_sound 1276672 128 c1276672) (checkChunk_sound 1276800 128 c1276800)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1276928 128 c1276928) (checkChunk_sound 1277056 128 c1277056)) (Checked.append (checkChunk_sound 1277184 128 c1277184) (checkChunk_sound 1277312 128 c1277312))) (Checked.append (Checked.append (checkChunk_sound 1277440 128 c1277440) (checkChunk_sound 1277568 128 c1277568)) (Checked.append (checkChunk_sound 1277696 128 c1277696) (checkChunk_sound 1277824 128 c1277824)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B024
