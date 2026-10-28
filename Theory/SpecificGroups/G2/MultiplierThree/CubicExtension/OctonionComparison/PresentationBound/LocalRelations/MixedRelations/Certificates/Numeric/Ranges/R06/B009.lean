module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1359872, 1368064).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B009
private theorem c1359872 : checkChunk 1359872 128 = true := by decide +kernel
private theorem c1360000 : checkChunk 1360000 128 = true := by decide +kernel
private theorem c1360128 : checkChunk 1360128 128 = true := by decide +kernel
private theorem c1360256 : checkChunk 1360256 128 = true := by decide +kernel
private theorem c1360384 : checkChunk 1360384 128 = true := by decide +kernel
private theorem c1360512 : checkChunk 1360512 128 = true := by decide +kernel
private theorem c1360640 : checkChunk 1360640 128 = true := by decide +kernel
private theorem c1360768 : checkChunk 1360768 128 = true := by decide +kernel
private theorem c1360896 : checkChunk 1360896 128 = true := by decide +kernel
private theorem c1361024 : checkChunk 1361024 128 = true := by decide +kernel
private theorem c1361152 : checkChunk 1361152 128 = true := by decide +kernel
private theorem c1361280 : checkChunk 1361280 128 = true := by decide +kernel
private theorem c1361408 : checkChunk 1361408 128 = true := by decide +kernel
private theorem c1361536 : checkChunk 1361536 128 = true := by decide +kernel
private theorem c1361664 : checkChunk 1361664 128 = true := by decide +kernel
private theorem c1361792 : checkChunk 1361792 128 = true := by decide +kernel
private theorem c1361920 : checkChunk 1361920 128 = true := by decide +kernel
private theorem c1362048 : checkChunk 1362048 128 = true := by decide +kernel
private theorem c1362176 : checkChunk 1362176 128 = true := by decide +kernel
private theorem c1362304 : checkChunk 1362304 128 = true := by decide +kernel
private theorem c1362432 : checkChunk 1362432 128 = true := by decide +kernel
private theorem c1362560 : checkChunk 1362560 128 = true := by decide +kernel
private theorem c1362688 : checkChunk 1362688 128 = true := by decide +kernel
private theorem c1362816 : checkChunk 1362816 128 = true := by decide +kernel
private theorem c1362944 : checkChunk 1362944 128 = true := by decide +kernel
private theorem c1363072 : checkChunk 1363072 128 = true := by decide +kernel
private theorem c1363200 : checkChunk 1363200 128 = true := by decide +kernel
private theorem c1363328 : checkChunk 1363328 128 = true := by decide +kernel
private theorem c1363456 : checkChunk 1363456 128 = true := by decide +kernel
private theorem c1363584 : checkChunk 1363584 128 = true := by decide +kernel
private theorem c1363712 : checkChunk 1363712 128 = true := by decide +kernel
private theorem c1363840 : checkChunk 1363840 128 = true := by decide +kernel
private theorem c1363968 : checkChunk 1363968 128 = true := by decide +kernel
private theorem c1364096 : checkChunk 1364096 128 = true := by decide +kernel
private theorem c1364224 : checkChunk 1364224 128 = true := by decide +kernel
private theorem c1364352 : checkChunk 1364352 128 = true := by decide +kernel
private theorem c1364480 : checkChunk 1364480 128 = true := by decide +kernel
private theorem c1364608 : checkChunk 1364608 128 = true := by decide +kernel
private theorem c1364736 : checkChunk 1364736 128 = true := by decide +kernel
private theorem c1364864 : checkChunk 1364864 128 = true := by decide +kernel
private theorem c1364992 : checkChunk 1364992 128 = true := by decide +kernel
private theorem c1365120 : checkChunk 1365120 128 = true := by decide +kernel
private theorem c1365248 : checkChunk 1365248 128 = true := by decide +kernel
private theorem c1365376 : checkChunk 1365376 128 = true := by decide +kernel
private theorem c1365504 : checkChunk 1365504 128 = true := by decide +kernel
private theorem c1365632 : checkChunk 1365632 128 = true := by decide +kernel
private theorem c1365760 : checkChunk 1365760 128 = true := by decide +kernel
private theorem c1365888 : checkChunk 1365888 128 = true := by decide +kernel
private theorem c1366016 : checkChunk 1366016 128 = true := by decide +kernel
private theorem c1366144 : checkChunk 1366144 128 = true := by decide +kernel
private theorem c1366272 : checkChunk 1366272 128 = true := by decide +kernel
private theorem c1366400 : checkChunk 1366400 128 = true := by decide +kernel
private theorem c1366528 : checkChunk 1366528 128 = true := by decide +kernel
private theorem c1366656 : checkChunk 1366656 128 = true := by decide +kernel
private theorem c1366784 : checkChunk 1366784 128 = true := by decide +kernel
private theorem c1366912 : checkChunk 1366912 128 = true := by decide +kernel
private theorem c1367040 : checkChunk 1367040 128 = true := by decide +kernel
private theorem c1367168 : checkChunk 1367168 128 = true := by decide +kernel
private theorem c1367296 : checkChunk 1367296 128 = true := by decide +kernel
private theorem c1367424 : checkChunk 1367424 128 = true := by decide +kernel
private theorem c1367552 : checkChunk 1367552 128 = true := by decide +kernel
private theorem c1367680 : checkChunk 1367680 128 = true := by decide +kernel
private theorem c1367808 : checkChunk 1367808 128 = true := by decide +kernel
private theorem c1367936 : checkChunk 1367936 128 = true := by decide +kernel

public theorem checked : Checked 1359872 1368064 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1359872 128 c1359872) (checkChunk_sound 1360000 128 c1360000)) (Checked.append (checkChunk_sound 1360128 128 c1360128) (checkChunk_sound 1360256 128 c1360256))) (Checked.append (Checked.append (checkChunk_sound 1360384 128 c1360384) (checkChunk_sound 1360512 128 c1360512)) (Checked.append (checkChunk_sound 1360640 128 c1360640) (checkChunk_sound 1360768 128 c1360768)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1360896 128 c1360896) (checkChunk_sound 1361024 128 c1361024)) (Checked.append (checkChunk_sound 1361152 128 c1361152) (checkChunk_sound 1361280 128 c1361280))) (Checked.append (Checked.append (checkChunk_sound 1361408 128 c1361408) (checkChunk_sound 1361536 128 c1361536)) (Checked.append (checkChunk_sound 1361664 128 c1361664) (checkChunk_sound 1361792 128 c1361792))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1361920 128 c1361920) (checkChunk_sound 1362048 128 c1362048)) (Checked.append (checkChunk_sound 1362176 128 c1362176) (checkChunk_sound 1362304 128 c1362304))) (Checked.append (Checked.append (checkChunk_sound 1362432 128 c1362432) (checkChunk_sound 1362560 128 c1362560)) (Checked.append (checkChunk_sound 1362688 128 c1362688) (checkChunk_sound 1362816 128 c1362816)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1362944 128 c1362944) (checkChunk_sound 1363072 128 c1363072)) (Checked.append (checkChunk_sound 1363200 128 c1363200) (checkChunk_sound 1363328 128 c1363328))) (Checked.append (Checked.append (checkChunk_sound 1363456 128 c1363456) (checkChunk_sound 1363584 128 c1363584)) (Checked.append (checkChunk_sound 1363712 128 c1363712) (checkChunk_sound 1363840 128 c1363840)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1363968 128 c1363968) (checkChunk_sound 1364096 128 c1364096)) (Checked.append (checkChunk_sound 1364224 128 c1364224) (checkChunk_sound 1364352 128 c1364352))) (Checked.append (Checked.append (checkChunk_sound 1364480 128 c1364480) (checkChunk_sound 1364608 128 c1364608)) (Checked.append (checkChunk_sound 1364736 128 c1364736) (checkChunk_sound 1364864 128 c1364864)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1364992 128 c1364992) (checkChunk_sound 1365120 128 c1365120)) (Checked.append (checkChunk_sound 1365248 128 c1365248) (checkChunk_sound 1365376 128 c1365376))) (Checked.append (Checked.append (checkChunk_sound 1365504 128 c1365504) (checkChunk_sound 1365632 128 c1365632)) (Checked.append (checkChunk_sound 1365760 128 c1365760) (checkChunk_sound 1365888 128 c1365888))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1366016 128 c1366016) (checkChunk_sound 1366144 128 c1366144)) (Checked.append (checkChunk_sound 1366272 128 c1366272) (checkChunk_sound 1366400 128 c1366400))) (Checked.append (Checked.append (checkChunk_sound 1366528 128 c1366528) (checkChunk_sound 1366656 128 c1366656)) (Checked.append (checkChunk_sound 1366784 128 c1366784) (checkChunk_sound 1366912 128 c1366912)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1367040 128 c1367040) (checkChunk_sound 1367168 128 c1367168)) (Checked.append (checkChunk_sound 1367296 128 c1367296) (checkChunk_sound 1367424 128 c1367424))) (Checked.append (Checked.append (checkChunk_sound 1367552 128 c1367552) (checkChunk_sound 1367680 128 c1367680)) (Checked.append (checkChunk_sound 1367808 128 c1367808) (checkChunk_sound 1367936 128 c1367936)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B009
