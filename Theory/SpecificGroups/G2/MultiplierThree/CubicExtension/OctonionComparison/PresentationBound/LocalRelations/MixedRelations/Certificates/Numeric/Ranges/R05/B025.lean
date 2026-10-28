module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1277952, 1286144).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B025
private theorem c1277952 : checkChunk 1277952 128 = true := by decide +kernel
private theorem c1278080 : checkChunk 1278080 128 = true := by decide +kernel
private theorem c1278208 : checkChunk 1278208 128 = true := by decide +kernel
private theorem c1278336 : checkChunk 1278336 128 = true := by decide +kernel
private theorem c1278464 : checkChunk 1278464 128 = true := by decide +kernel
private theorem c1278592 : checkChunk 1278592 128 = true := by decide +kernel
private theorem c1278720 : checkChunk 1278720 128 = true := by decide +kernel
private theorem c1278848 : checkChunk 1278848 128 = true := by decide +kernel
private theorem c1278976 : checkChunk 1278976 128 = true := by decide +kernel
private theorem c1279104 : checkChunk 1279104 128 = true := by decide +kernel
private theorem c1279232 : checkChunk 1279232 128 = true := by decide +kernel
private theorem c1279360 : checkChunk 1279360 128 = true := by decide +kernel
private theorem c1279488 : checkChunk 1279488 128 = true := by decide +kernel
private theorem c1279616 : checkChunk 1279616 128 = true := by decide +kernel
private theorem c1279744 : checkChunk 1279744 128 = true := by decide +kernel
private theorem c1279872 : checkChunk 1279872 128 = true := by decide +kernel
private theorem c1280000 : checkChunk 1280000 128 = true := by decide +kernel
private theorem c1280128 : checkChunk 1280128 128 = true := by decide +kernel
private theorem c1280256 : checkChunk 1280256 128 = true := by decide +kernel
private theorem c1280384 : checkChunk 1280384 128 = true := by decide +kernel
private theorem c1280512 : checkChunk 1280512 128 = true := by decide +kernel
private theorem c1280640 : checkChunk 1280640 128 = true := by decide +kernel
private theorem c1280768 : checkChunk 1280768 128 = true := by decide +kernel
private theorem c1280896 : checkChunk 1280896 128 = true := by decide +kernel
private theorem c1281024 : checkChunk 1281024 128 = true := by decide +kernel
private theorem c1281152 : checkChunk 1281152 128 = true := by decide +kernel
private theorem c1281280 : checkChunk 1281280 128 = true := by decide +kernel
private theorem c1281408 : checkChunk 1281408 128 = true := by decide +kernel
private theorem c1281536 : checkChunk 1281536 128 = true := by decide +kernel
private theorem c1281664 : checkChunk 1281664 128 = true := by decide +kernel
private theorem c1281792 : checkChunk 1281792 128 = true := by decide +kernel
private theorem c1281920 : checkChunk 1281920 128 = true := by decide +kernel
private theorem c1282048 : checkChunk 1282048 128 = true := by decide +kernel
private theorem c1282176 : checkChunk 1282176 128 = true := by decide +kernel
private theorem c1282304 : checkChunk 1282304 128 = true := by decide +kernel
private theorem c1282432 : checkChunk 1282432 128 = true := by decide +kernel
private theorem c1282560 : checkChunk 1282560 128 = true := by decide +kernel
private theorem c1282688 : checkChunk 1282688 128 = true := by decide +kernel
private theorem c1282816 : checkChunk 1282816 128 = true := by decide +kernel
private theorem c1282944 : checkChunk 1282944 128 = true := by decide +kernel
private theorem c1283072 : checkChunk 1283072 128 = true := by decide +kernel
private theorem c1283200 : checkChunk 1283200 128 = true := by decide +kernel
private theorem c1283328 : checkChunk 1283328 128 = true := by decide +kernel
private theorem c1283456 : checkChunk 1283456 128 = true := by decide +kernel
private theorem c1283584 : checkChunk 1283584 128 = true := by decide +kernel
private theorem c1283712 : checkChunk 1283712 128 = true := by decide +kernel
private theorem c1283840 : checkChunk 1283840 128 = true := by decide +kernel
private theorem c1283968 : checkChunk 1283968 128 = true := by decide +kernel
private theorem c1284096 : checkChunk 1284096 128 = true := by decide +kernel
private theorem c1284224 : checkChunk 1284224 128 = true := by decide +kernel
private theorem c1284352 : checkChunk 1284352 128 = true := by decide +kernel
private theorem c1284480 : checkChunk 1284480 128 = true := by decide +kernel
private theorem c1284608 : checkChunk 1284608 128 = true := by decide +kernel
private theorem c1284736 : checkChunk 1284736 128 = true := by decide +kernel
private theorem c1284864 : checkChunk 1284864 128 = true := by decide +kernel
private theorem c1284992 : checkChunk 1284992 128 = true := by decide +kernel
private theorem c1285120 : checkChunk 1285120 128 = true := by decide +kernel
private theorem c1285248 : checkChunk 1285248 128 = true := by decide +kernel
private theorem c1285376 : checkChunk 1285376 128 = true := by decide +kernel
private theorem c1285504 : checkChunk 1285504 128 = true := by decide +kernel
private theorem c1285632 : checkChunk 1285632 128 = true := by decide +kernel
private theorem c1285760 : checkChunk 1285760 128 = true := by decide +kernel
private theorem c1285888 : checkChunk 1285888 128 = true := by decide +kernel
private theorem c1286016 : checkChunk 1286016 128 = true := by decide +kernel

public theorem checked : Checked 1277952 1286144 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1277952 128 c1277952) (checkChunk_sound 1278080 128 c1278080)) (Checked.append (checkChunk_sound 1278208 128 c1278208) (checkChunk_sound 1278336 128 c1278336))) (Checked.append (Checked.append (checkChunk_sound 1278464 128 c1278464) (checkChunk_sound 1278592 128 c1278592)) (Checked.append (checkChunk_sound 1278720 128 c1278720) (checkChunk_sound 1278848 128 c1278848)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1278976 128 c1278976) (checkChunk_sound 1279104 128 c1279104)) (Checked.append (checkChunk_sound 1279232 128 c1279232) (checkChunk_sound 1279360 128 c1279360))) (Checked.append (Checked.append (checkChunk_sound 1279488 128 c1279488) (checkChunk_sound 1279616 128 c1279616)) (Checked.append (checkChunk_sound 1279744 128 c1279744) (checkChunk_sound 1279872 128 c1279872))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1280000 128 c1280000) (checkChunk_sound 1280128 128 c1280128)) (Checked.append (checkChunk_sound 1280256 128 c1280256) (checkChunk_sound 1280384 128 c1280384))) (Checked.append (Checked.append (checkChunk_sound 1280512 128 c1280512) (checkChunk_sound 1280640 128 c1280640)) (Checked.append (checkChunk_sound 1280768 128 c1280768) (checkChunk_sound 1280896 128 c1280896)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1281024 128 c1281024) (checkChunk_sound 1281152 128 c1281152)) (Checked.append (checkChunk_sound 1281280 128 c1281280) (checkChunk_sound 1281408 128 c1281408))) (Checked.append (Checked.append (checkChunk_sound 1281536 128 c1281536) (checkChunk_sound 1281664 128 c1281664)) (Checked.append (checkChunk_sound 1281792 128 c1281792) (checkChunk_sound 1281920 128 c1281920)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1282048 128 c1282048) (checkChunk_sound 1282176 128 c1282176)) (Checked.append (checkChunk_sound 1282304 128 c1282304) (checkChunk_sound 1282432 128 c1282432))) (Checked.append (Checked.append (checkChunk_sound 1282560 128 c1282560) (checkChunk_sound 1282688 128 c1282688)) (Checked.append (checkChunk_sound 1282816 128 c1282816) (checkChunk_sound 1282944 128 c1282944)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1283072 128 c1283072) (checkChunk_sound 1283200 128 c1283200)) (Checked.append (checkChunk_sound 1283328 128 c1283328) (checkChunk_sound 1283456 128 c1283456))) (Checked.append (Checked.append (checkChunk_sound 1283584 128 c1283584) (checkChunk_sound 1283712 128 c1283712)) (Checked.append (checkChunk_sound 1283840 128 c1283840) (checkChunk_sound 1283968 128 c1283968))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1284096 128 c1284096) (checkChunk_sound 1284224 128 c1284224)) (Checked.append (checkChunk_sound 1284352 128 c1284352) (checkChunk_sound 1284480 128 c1284480))) (Checked.append (Checked.append (checkChunk_sound 1284608 128 c1284608) (checkChunk_sound 1284736 128 c1284736)) (Checked.append (checkChunk_sound 1284864 128 c1284864) (checkChunk_sound 1284992 128 c1284992)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1285120 128 c1285120) (checkChunk_sound 1285248 128 c1285248)) (Checked.append (checkChunk_sound 1285376 128 c1285376) (checkChunk_sound 1285504 128 c1285504))) (Checked.append (Checked.append (checkChunk_sound 1285632 128 c1285632) (checkChunk_sound 1285760 128 c1285760)) (Checked.append (checkChunk_sound 1285888 128 c1285888) (checkChunk_sound 1286016 128 c1286016)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B025
