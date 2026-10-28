module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1384448, 1392640).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B012
private theorem c1384448 : checkChunk 1384448 128 = true := by decide +kernel
private theorem c1384576 : checkChunk 1384576 128 = true := by decide +kernel
private theorem c1384704 : checkChunk 1384704 128 = true := by decide +kernel
private theorem c1384832 : checkChunk 1384832 128 = true := by decide +kernel
private theorem c1384960 : checkChunk 1384960 128 = true := by decide +kernel
private theorem c1385088 : checkChunk 1385088 128 = true := by decide +kernel
private theorem c1385216 : checkChunk 1385216 128 = true := by decide +kernel
private theorem c1385344 : checkChunk 1385344 128 = true := by decide +kernel
private theorem c1385472 : checkChunk 1385472 128 = true := by decide +kernel
private theorem c1385600 : checkChunk 1385600 128 = true := by decide +kernel
private theorem c1385728 : checkChunk 1385728 128 = true := by decide +kernel
private theorem c1385856 : checkChunk 1385856 128 = true := by decide +kernel
private theorem c1385984 : checkChunk 1385984 128 = true := by decide +kernel
private theorem c1386112 : checkChunk 1386112 128 = true := by decide +kernel
private theorem c1386240 : checkChunk 1386240 128 = true := by decide +kernel
private theorem c1386368 : checkChunk 1386368 128 = true := by decide +kernel
private theorem c1386496 : checkChunk 1386496 128 = true := by decide +kernel
private theorem c1386624 : checkChunk 1386624 128 = true := by decide +kernel
private theorem c1386752 : checkChunk 1386752 128 = true := by decide +kernel
private theorem c1386880 : checkChunk 1386880 128 = true := by decide +kernel
private theorem c1387008 : checkChunk 1387008 128 = true := by decide +kernel
private theorem c1387136 : checkChunk 1387136 128 = true := by decide +kernel
private theorem c1387264 : checkChunk 1387264 128 = true := by decide +kernel
private theorem c1387392 : checkChunk 1387392 128 = true := by decide +kernel
private theorem c1387520 : checkChunk 1387520 128 = true := by decide +kernel
private theorem c1387648 : checkChunk 1387648 128 = true := by decide +kernel
private theorem c1387776 : checkChunk 1387776 128 = true := by decide +kernel
private theorem c1387904 : checkChunk 1387904 128 = true := by decide +kernel
private theorem c1388032 : checkChunk 1388032 128 = true := by decide +kernel
private theorem c1388160 : checkChunk 1388160 128 = true := by decide +kernel
private theorem c1388288 : checkChunk 1388288 128 = true := by decide +kernel
private theorem c1388416 : checkChunk 1388416 128 = true := by decide +kernel
private theorem c1388544 : checkChunk 1388544 128 = true := by decide +kernel
private theorem c1388672 : checkChunk 1388672 128 = true := by decide +kernel
private theorem c1388800 : checkChunk 1388800 128 = true := by decide +kernel
private theorem c1388928 : checkChunk 1388928 128 = true := by decide +kernel
private theorem c1389056 : checkChunk 1389056 128 = true := by decide +kernel
private theorem c1389184 : checkChunk 1389184 128 = true := by decide +kernel
private theorem c1389312 : checkChunk 1389312 128 = true := by decide +kernel
private theorem c1389440 : checkChunk 1389440 128 = true := by decide +kernel
private theorem c1389568 : checkChunk 1389568 128 = true := by decide +kernel
private theorem c1389696 : checkChunk 1389696 128 = true := by decide +kernel
private theorem c1389824 : checkChunk 1389824 128 = true := by decide +kernel
private theorem c1389952 : checkChunk 1389952 128 = true := by decide +kernel
private theorem c1390080 : checkChunk 1390080 128 = true := by decide +kernel
private theorem c1390208 : checkChunk 1390208 128 = true := by decide +kernel
private theorem c1390336 : checkChunk 1390336 128 = true := by decide +kernel
private theorem c1390464 : checkChunk 1390464 128 = true := by decide +kernel
private theorem c1390592 : checkChunk 1390592 128 = true := by decide +kernel
private theorem c1390720 : checkChunk 1390720 128 = true := by decide +kernel
private theorem c1390848 : checkChunk 1390848 128 = true := by decide +kernel
private theorem c1390976 : checkChunk 1390976 128 = true := by decide +kernel
private theorem c1391104 : checkChunk 1391104 128 = true := by decide +kernel
private theorem c1391232 : checkChunk 1391232 128 = true := by decide +kernel
private theorem c1391360 : checkChunk 1391360 128 = true := by decide +kernel
private theorem c1391488 : checkChunk 1391488 128 = true := by decide +kernel
private theorem c1391616 : checkChunk 1391616 128 = true := by decide +kernel
private theorem c1391744 : checkChunk 1391744 128 = true := by decide +kernel
private theorem c1391872 : checkChunk 1391872 128 = true := by decide +kernel
private theorem c1392000 : checkChunk 1392000 128 = true := by decide +kernel
private theorem c1392128 : checkChunk 1392128 128 = true := by decide +kernel
private theorem c1392256 : checkChunk 1392256 128 = true := by decide +kernel
private theorem c1392384 : checkChunk 1392384 128 = true := by decide +kernel
private theorem c1392512 : checkChunk 1392512 128 = true := by decide +kernel

public theorem checked : Checked 1384448 1392640 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1384448 128 c1384448) (checkChunk_sound 1384576 128 c1384576)) (Checked.append (checkChunk_sound 1384704 128 c1384704) (checkChunk_sound 1384832 128 c1384832))) (Checked.append (Checked.append (checkChunk_sound 1384960 128 c1384960) (checkChunk_sound 1385088 128 c1385088)) (Checked.append (checkChunk_sound 1385216 128 c1385216) (checkChunk_sound 1385344 128 c1385344)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1385472 128 c1385472) (checkChunk_sound 1385600 128 c1385600)) (Checked.append (checkChunk_sound 1385728 128 c1385728) (checkChunk_sound 1385856 128 c1385856))) (Checked.append (Checked.append (checkChunk_sound 1385984 128 c1385984) (checkChunk_sound 1386112 128 c1386112)) (Checked.append (checkChunk_sound 1386240 128 c1386240) (checkChunk_sound 1386368 128 c1386368))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1386496 128 c1386496) (checkChunk_sound 1386624 128 c1386624)) (Checked.append (checkChunk_sound 1386752 128 c1386752) (checkChunk_sound 1386880 128 c1386880))) (Checked.append (Checked.append (checkChunk_sound 1387008 128 c1387008) (checkChunk_sound 1387136 128 c1387136)) (Checked.append (checkChunk_sound 1387264 128 c1387264) (checkChunk_sound 1387392 128 c1387392)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1387520 128 c1387520) (checkChunk_sound 1387648 128 c1387648)) (Checked.append (checkChunk_sound 1387776 128 c1387776) (checkChunk_sound 1387904 128 c1387904))) (Checked.append (Checked.append (checkChunk_sound 1388032 128 c1388032) (checkChunk_sound 1388160 128 c1388160)) (Checked.append (checkChunk_sound 1388288 128 c1388288) (checkChunk_sound 1388416 128 c1388416)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1388544 128 c1388544) (checkChunk_sound 1388672 128 c1388672)) (Checked.append (checkChunk_sound 1388800 128 c1388800) (checkChunk_sound 1388928 128 c1388928))) (Checked.append (Checked.append (checkChunk_sound 1389056 128 c1389056) (checkChunk_sound 1389184 128 c1389184)) (Checked.append (checkChunk_sound 1389312 128 c1389312) (checkChunk_sound 1389440 128 c1389440)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1389568 128 c1389568) (checkChunk_sound 1389696 128 c1389696)) (Checked.append (checkChunk_sound 1389824 128 c1389824) (checkChunk_sound 1389952 128 c1389952))) (Checked.append (Checked.append (checkChunk_sound 1390080 128 c1390080) (checkChunk_sound 1390208 128 c1390208)) (Checked.append (checkChunk_sound 1390336 128 c1390336) (checkChunk_sound 1390464 128 c1390464))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1390592 128 c1390592) (checkChunk_sound 1390720 128 c1390720)) (Checked.append (checkChunk_sound 1390848 128 c1390848) (checkChunk_sound 1390976 128 c1390976))) (Checked.append (Checked.append (checkChunk_sound 1391104 128 c1391104) (checkChunk_sound 1391232 128 c1391232)) (Checked.append (checkChunk_sound 1391360 128 c1391360) (checkChunk_sound 1391488 128 c1391488)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1391616 128 c1391616) (checkChunk_sound 1391744 128 c1391744)) (Checked.append (checkChunk_sound 1391872 128 c1391872) (checkChunk_sound 1392000 128 c1392000))) (Checked.append (Checked.append (checkChunk_sound 1392128 128 c1392128) (checkChunk_sound 1392256 128 c1392256)) (Checked.append (checkChunk_sound 1392384 128 c1392384) (checkChunk_sound 1392512 128 c1392512)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B012
