module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1294336, 1302528).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B001
private theorem c1294336 : checkChunk 1294336 128 = true := by decide +kernel
private theorem c1294464 : checkChunk 1294464 128 = true := by decide +kernel
private theorem c1294592 : checkChunk 1294592 128 = true := by decide +kernel
private theorem c1294720 : checkChunk 1294720 128 = true := by decide +kernel
private theorem c1294848 : checkChunk 1294848 128 = true := by decide +kernel
private theorem c1294976 : checkChunk 1294976 128 = true := by decide +kernel
private theorem c1295104 : checkChunk 1295104 128 = true := by decide +kernel
private theorem c1295232 : checkChunk 1295232 128 = true := by decide +kernel
private theorem c1295360 : checkChunk 1295360 128 = true := by decide +kernel
private theorem c1295488 : checkChunk 1295488 128 = true := by decide +kernel
private theorem c1295616 : checkChunk 1295616 128 = true := by decide +kernel
private theorem c1295744 : checkChunk 1295744 128 = true := by decide +kernel
private theorem c1295872 : checkChunk 1295872 128 = true := by decide +kernel
private theorem c1296000 : checkChunk 1296000 128 = true := by decide +kernel
private theorem c1296128 : checkChunk 1296128 128 = true := by decide +kernel
private theorem c1296256 : checkChunk 1296256 128 = true := by decide +kernel
private theorem c1296384 : checkChunk 1296384 128 = true := by decide +kernel
private theorem c1296512 : checkChunk 1296512 128 = true := by decide +kernel
private theorem c1296640 : checkChunk 1296640 128 = true := by decide +kernel
private theorem c1296768 : checkChunk 1296768 128 = true := by decide +kernel
private theorem c1296896 : checkChunk 1296896 128 = true := by decide +kernel
private theorem c1297024 : checkChunk 1297024 128 = true := by decide +kernel
private theorem c1297152 : checkChunk 1297152 128 = true := by decide +kernel
private theorem c1297280 : checkChunk 1297280 128 = true := by decide +kernel
private theorem c1297408 : checkChunk 1297408 128 = true := by decide +kernel
private theorem c1297536 : checkChunk 1297536 128 = true := by decide +kernel
private theorem c1297664 : checkChunk 1297664 128 = true := by decide +kernel
private theorem c1297792 : checkChunk 1297792 128 = true := by decide +kernel
private theorem c1297920 : checkChunk 1297920 128 = true := by decide +kernel
private theorem c1298048 : checkChunk 1298048 128 = true := by decide +kernel
private theorem c1298176 : checkChunk 1298176 128 = true := by decide +kernel
private theorem c1298304 : checkChunk 1298304 128 = true := by decide +kernel
private theorem c1298432 : checkChunk 1298432 128 = true := by decide +kernel
private theorem c1298560 : checkChunk 1298560 128 = true := by decide +kernel
private theorem c1298688 : checkChunk 1298688 128 = true := by decide +kernel
private theorem c1298816 : checkChunk 1298816 128 = true := by decide +kernel
private theorem c1298944 : checkChunk 1298944 128 = true := by decide +kernel
private theorem c1299072 : checkChunk 1299072 128 = true := by decide +kernel
private theorem c1299200 : checkChunk 1299200 128 = true := by decide +kernel
private theorem c1299328 : checkChunk 1299328 128 = true := by decide +kernel
private theorem c1299456 : checkChunk 1299456 128 = true := by decide +kernel
private theorem c1299584 : checkChunk 1299584 128 = true := by decide +kernel
private theorem c1299712 : checkChunk 1299712 128 = true := by decide +kernel
private theorem c1299840 : checkChunk 1299840 128 = true := by decide +kernel
private theorem c1299968 : checkChunk 1299968 128 = true := by decide +kernel
private theorem c1300096 : checkChunk 1300096 128 = true := by decide +kernel
private theorem c1300224 : checkChunk 1300224 128 = true := by decide +kernel
private theorem c1300352 : checkChunk 1300352 128 = true := by decide +kernel
private theorem c1300480 : checkChunk 1300480 128 = true := by decide +kernel
private theorem c1300608 : checkChunk 1300608 128 = true := by decide +kernel
private theorem c1300736 : checkChunk 1300736 128 = true := by decide +kernel
private theorem c1300864 : checkChunk 1300864 128 = true := by decide +kernel
private theorem c1300992 : checkChunk 1300992 128 = true := by decide +kernel
private theorem c1301120 : checkChunk 1301120 128 = true := by decide +kernel
private theorem c1301248 : checkChunk 1301248 128 = true := by decide +kernel
private theorem c1301376 : checkChunk 1301376 128 = true := by decide +kernel
private theorem c1301504 : checkChunk 1301504 128 = true := by decide +kernel
private theorem c1301632 : checkChunk 1301632 128 = true := by decide +kernel
private theorem c1301760 : checkChunk 1301760 128 = true := by decide +kernel
private theorem c1301888 : checkChunk 1301888 128 = true := by decide +kernel
private theorem c1302016 : checkChunk 1302016 128 = true := by decide +kernel
private theorem c1302144 : checkChunk 1302144 128 = true := by decide +kernel
private theorem c1302272 : checkChunk 1302272 128 = true := by decide +kernel
private theorem c1302400 : checkChunk 1302400 128 = true := by decide +kernel

public theorem checked : Checked 1294336 1302528 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1294336 128 c1294336) (checkChunk_sound 1294464 128 c1294464)) (Checked.append (checkChunk_sound 1294592 128 c1294592) (checkChunk_sound 1294720 128 c1294720))) (Checked.append (Checked.append (checkChunk_sound 1294848 128 c1294848) (checkChunk_sound 1294976 128 c1294976)) (Checked.append (checkChunk_sound 1295104 128 c1295104) (checkChunk_sound 1295232 128 c1295232)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1295360 128 c1295360) (checkChunk_sound 1295488 128 c1295488)) (Checked.append (checkChunk_sound 1295616 128 c1295616) (checkChunk_sound 1295744 128 c1295744))) (Checked.append (Checked.append (checkChunk_sound 1295872 128 c1295872) (checkChunk_sound 1296000 128 c1296000)) (Checked.append (checkChunk_sound 1296128 128 c1296128) (checkChunk_sound 1296256 128 c1296256))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1296384 128 c1296384) (checkChunk_sound 1296512 128 c1296512)) (Checked.append (checkChunk_sound 1296640 128 c1296640) (checkChunk_sound 1296768 128 c1296768))) (Checked.append (Checked.append (checkChunk_sound 1296896 128 c1296896) (checkChunk_sound 1297024 128 c1297024)) (Checked.append (checkChunk_sound 1297152 128 c1297152) (checkChunk_sound 1297280 128 c1297280)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1297408 128 c1297408) (checkChunk_sound 1297536 128 c1297536)) (Checked.append (checkChunk_sound 1297664 128 c1297664) (checkChunk_sound 1297792 128 c1297792))) (Checked.append (Checked.append (checkChunk_sound 1297920 128 c1297920) (checkChunk_sound 1298048 128 c1298048)) (Checked.append (checkChunk_sound 1298176 128 c1298176) (checkChunk_sound 1298304 128 c1298304)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1298432 128 c1298432) (checkChunk_sound 1298560 128 c1298560)) (Checked.append (checkChunk_sound 1298688 128 c1298688) (checkChunk_sound 1298816 128 c1298816))) (Checked.append (Checked.append (checkChunk_sound 1298944 128 c1298944) (checkChunk_sound 1299072 128 c1299072)) (Checked.append (checkChunk_sound 1299200 128 c1299200) (checkChunk_sound 1299328 128 c1299328)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1299456 128 c1299456) (checkChunk_sound 1299584 128 c1299584)) (Checked.append (checkChunk_sound 1299712 128 c1299712) (checkChunk_sound 1299840 128 c1299840))) (Checked.append (Checked.append (checkChunk_sound 1299968 128 c1299968) (checkChunk_sound 1300096 128 c1300096)) (Checked.append (checkChunk_sound 1300224 128 c1300224) (checkChunk_sound 1300352 128 c1300352))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1300480 128 c1300480) (checkChunk_sound 1300608 128 c1300608)) (Checked.append (checkChunk_sound 1300736 128 c1300736) (checkChunk_sound 1300864 128 c1300864))) (Checked.append (Checked.append (checkChunk_sound 1300992 128 c1300992) (checkChunk_sound 1301120 128 c1301120)) (Checked.append (checkChunk_sound 1301248 128 c1301248) (checkChunk_sound 1301376 128 c1301376)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1301504 128 c1301504) (checkChunk_sound 1301632 128 c1301632)) (Checked.append (checkChunk_sound 1301760 128 c1301760) (checkChunk_sound 1301888 128 c1301888))) (Checked.append (Checked.append (checkChunk_sound 1302016 128 c1302016) (checkChunk_sound 1302144 128 c1302144)) (Checked.append (checkChunk_sound 1302272 128 c1302272) (checkChunk_sound 1302400 128 c1302400)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B001
