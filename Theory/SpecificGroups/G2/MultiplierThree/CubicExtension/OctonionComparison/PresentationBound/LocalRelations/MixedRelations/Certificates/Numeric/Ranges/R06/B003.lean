module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1310720, 1318912).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B003
private theorem c1310720 : checkChunk 1310720 128 = true := by decide +kernel
private theorem c1310848 : checkChunk 1310848 128 = true := by decide +kernel
private theorem c1310976 : checkChunk 1310976 128 = true := by decide +kernel
private theorem c1311104 : checkChunk 1311104 128 = true := by decide +kernel
private theorem c1311232 : checkChunk 1311232 128 = true := by decide +kernel
private theorem c1311360 : checkChunk 1311360 128 = true := by decide +kernel
private theorem c1311488 : checkChunk 1311488 128 = true := by decide +kernel
private theorem c1311616 : checkChunk 1311616 128 = true := by decide +kernel
private theorem c1311744 : checkChunk 1311744 128 = true := by decide +kernel
private theorem c1311872 : checkChunk 1311872 128 = true := by decide +kernel
private theorem c1312000 : checkChunk 1312000 128 = true := by decide +kernel
private theorem c1312128 : checkChunk 1312128 128 = true := by decide +kernel
private theorem c1312256 : checkChunk 1312256 128 = true := by decide +kernel
private theorem c1312384 : checkChunk 1312384 128 = true := by decide +kernel
private theorem c1312512 : checkChunk 1312512 128 = true := by decide +kernel
private theorem c1312640 : checkChunk 1312640 128 = true := by decide +kernel
private theorem c1312768 : checkChunk 1312768 128 = true := by decide +kernel
private theorem c1312896 : checkChunk 1312896 128 = true := by decide +kernel
private theorem c1313024 : checkChunk 1313024 128 = true := by decide +kernel
private theorem c1313152 : checkChunk 1313152 128 = true := by decide +kernel
private theorem c1313280 : checkChunk 1313280 128 = true := by decide +kernel
private theorem c1313408 : checkChunk 1313408 128 = true := by decide +kernel
private theorem c1313536 : checkChunk 1313536 128 = true := by decide +kernel
private theorem c1313664 : checkChunk 1313664 128 = true := by decide +kernel
private theorem c1313792 : checkChunk 1313792 128 = true := by decide +kernel
private theorem c1313920 : checkChunk 1313920 128 = true := by decide +kernel
private theorem c1314048 : checkChunk 1314048 128 = true := by decide +kernel
private theorem c1314176 : checkChunk 1314176 128 = true := by decide +kernel
private theorem c1314304 : checkChunk 1314304 128 = true := by decide +kernel
private theorem c1314432 : checkChunk 1314432 128 = true := by decide +kernel
private theorem c1314560 : checkChunk 1314560 128 = true := by decide +kernel
private theorem c1314688 : checkChunk 1314688 128 = true := by decide +kernel
private theorem c1314816 : checkChunk 1314816 128 = true := by decide +kernel
private theorem c1314944 : checkChunk 1314944 128 = true := by decide +kernel
private theorem c1315072 : checkChunk 1315072 128 = true := by decide +kernel
private theorem c1315200 : checkChunk 1315200 128 = true := by decide +kernel
private theorem c1315328 : checkChunk 1315328 128 = true := by decide +kernel
private theorem c1315456 : checkChunk 1315456 128 = true := by decide +kernel
private theorem c1315584 : checkChunk 1315584 128 = true := by decide +kernel
private theorem c1315712 : checkChunk 1315712 128 = true := by decide +kernel
private theorem c1315840 : checkChunk 1315840 128 = true := by decide +kernel
private theorem c1315968 : checkChunk 1315968 128 = true := by decide +kernel
private theorem c1316096 : checkChunk 1316096 128 = true := by decide +kernel
private theorem c1316224 : checkChunk 1316224 128 = true := by decide +kernel
private theorem c1316352 : checkChunk 1316352 128 = true := by decide +kernel
private theorem c1316480 : checkChunk 1316480 128 = true := by decide +kernel
private theorem c1316608 : checkChunk 1316608 128 = true := by decide +kernel
private theorem c1316736 : checkChunk 1316736 128 = true := by decide +kernel
private theorem c1316864 : checkChunk 1316864 128 = true := by decide +kernel
private theorem c1316992 : checkChunk 1316992 128 = true := by decide +kernel
private theorem c1317120 : checkChunk 1317120 128 = true := by decide +kernel
private theorem c1317248 : checkChunk 1317248 128 = true := by decide +kernel
private theorem c1317376 : checkChunk 1317376 128 = true := by decide +kernel
private theorem c1317504 : checkChunk 1317504 128 = true := by decide +kernel
private theorem c1317632 : checkChunk 1317632 128 = true := by decide +kernel
private theorem c1317760 : checkChunk 1317760 128 = true := by decide +kernel
private theorem c1317888 : checkChunk 1317888 128 = true := by decide +kernel
private theorem c1318016 : checkChunk 1318016 128 = true := by decide +kernel
private theorem c1318144 : checkChunk 1318144 128 = true := by decide +kernel
private theorem c1318272 : checkChunk 1318272 128 = true := by decide +kernel
private theorem c1318400 : checkChunk 1318400 128 = true := by decide +kernel
private theorem c1318528 : checkChunk 1318528 128 = true := by decide +kernel
private theorem c1318656 : checkChunk 1318656 128 = true := by decide +kernel
private theorem c1318784 : checkChunk 1318784 128 = true := by decide +kernel

public theorem checked : Checked 1310720 1318912 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1310720 128 c1310720) (checkChunk_sound 1310848 128 c1310848)) (Checked.append (checkChunk_sound 1310976 128 c1310976) (checkChunk_sound 1311104 128 c1311104))) (Checked.append (Checked.append (checkChunk_sound 1311232 128 c1311232) (checkChunk_sound 1311360 128 c1311360)) (Checked.append (checkChunk_sound 1311488 128 c1311488) (checkChunk_sound 1311616 128 c1311616)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1311744 128 c1311744) (checkChunk_sound 1311872 128 c1311872)) (Checked.append (checkChunk_sound 1312000 128 c1312000) (checkChunk_sound 1312128 128 c1312128))) (Checked.append (Checked.append (checkChunk_sound 1312256 128 c1312256) (checkChunk_sound 1312384 128 c1312384)) (Checked.append (checkChunk_sound 1312512 128 c1312512) (checkChunk_sound 1312640 128 c1312640))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1312768 128 c1312768) (checkChunk_sound 1312896 128 c1312896)) (Checked.append (checkChunk_sound 1313024 128 c1313024) (checkChunk_sound 1313152 128 c1313152))) (Checked.append (Checked.append (checkChunk_sound 1313280 128 c1313280) (checkChunk_sound 1313408 128 c1313408)) (Checked.append (checkChunk_sound 1313536 128 c1313536) (checkChunk_sound 1313664 128 c1313664)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1313792 128 c1313792) (checkChunk_sound 1313920 128 c1313920)) (Checked.append (checkChunk_sound 1314048 128 c1314048) (checkChunk_sound 1314176 128 c1314176))) (Checked.append (Checked.append (checkChunk_sound 1314304 128 c1314304) (checkChunk_sound 1314432 128 c1314432)) (Checked.append (checkChunk_sound 1314560 128 c1314560) (checkChunk_sound 1314688 128 c1314688)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1314816 128 c1314816) (checkChunk_sound 1314944 128 c1314944)) (Checked.append (checkChunk_sound 1315072 128 c1315072) (checkChunk_sound 1315200 128 c1315200))) (Checked.append (Checked.append (checkChunk_sound 1315328 128 c1315328) (checkChunk_sound 1315456 128 c1315456)) (Checked.append (checkChunk_sound 1315584 128 c1315584) (checkChunk_sound 1315712 128 c1315712)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1315840 128 c1315840) (checkChunk_sound 1315968 128 c1315968)) (Checked.append (checkChunk_sound 1316096 128 c1316096) (checkChunk_sound 1316224 128 c1316224))) (Checked.append (Checked.append (checkChunk_sound 1316352 128 c1316352) (checkChunk_sound 1316480 128 c1316480)) (Checked.append (checkChunk_sound 1316608 128 c1316608) (checkChunk_sound 1316736 128 c1316736))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1316864 128 c1316864) (checkChunk_sound 1316992 128 c1316992)) (Checked.append (checkChunk_sound 1317120 128 c1317120) (checkChunk_sound 1317248 128 c1317248))) (Checked.append (Checked.append (checkChunk_sound 1317376 128 c1317376) (checkChunk_sound 1317504 128 c1317504)) (Checked.append (checkChunk_sound 1317632 128 c1317632) (checkChunk_sound 1317760 128 c1317760)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1317888 128 c1317888) (checkChunk_sound 1318016 128 c1318016)) (Checked.append (checkChunk_sound 1318144 128 c1318144) (checkChunk_sound 1318272 128 c1318272))) (Checked.append (Checked.append (checkChunk_sound 1318400 128 c1318400) (checkChunk_sound 1318528 128 c1318528)) (Checked.append (checkChunk_sound 1318656 128 c1318656) (checkChunk_sound 1318784 128 c1318784)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B003
