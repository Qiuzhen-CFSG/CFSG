module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1368064, 1376256).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B010
private theorem c1368064 : checkChunk 1368064 128 = true := by decide +kernel
private theorem c1368192 : checkChunk 1368192 128 = true := by decide +kernel
private theorem c1368320 : checkChunk 1368320 128 = true := by decide +kernel
private theorem c1368448 : checkChunk 1368448 128 = true := by decide +kernel
private theorem c1368576 : checkChunk 1368576 128 = true := by decide +kernel
private theorem c1368704 : checkChunk 1368704 128 = true := by decide +kernel
private theorem c1368832 : checkChunk 1368832 128 = true := by decide +kernel
private theorem c1368960 : checkChunk 1368960 128 = true := by decide +kernel
private theorem c1369088 : checkChunk 1369088 128 = true := by decide +kernel
private theorem c1369216 : checkChunk 1369216 128 = true := by decide +kernel
private theorem c1369344 : checkChunk 1369344 128 = true := by decide +kernel
private theorem c1369472 : checkChunk 1369472 128 = true := by decide +kernel
private theorem c1369600 : checkChunk 1369600 128 = true := by decide +kernel
private theorem c1369728 : checkChunk 1369728 128 = true := by decide +kernel
private theorem c1369856 : checkChunk 1369856 128 = true := by decide +kernel
private theorem c1369984 : checkChunk 1369984 128 = true := by decide +kernel
private theorem c1370112 : checkChunk 1370112 128 = true := by decide +kernel
private theorem c1370240 : checkChunk 1370240 128 = true := by decide +kernel
private theorem c1370368 : checkChunk 1370368 128 = true := by decide +kernel
private theorem c1370496 : checkChunk 1370496 128 = true := by decide +kernel
private theorem c1370624 : checkChunk 1370624 128 = true := by decide +kernel
private theorem c1370752 : checkChunk 1370752 128 = true := by decide +kernel
private theorem c1370880 : checkChunk 1370880 128 = true := by decide +kernel
private theorem c1371008 : checkChunk 1371008 128 = true := by decide +kernel
private theorem c1371136 : checkChunk 1371136 128 = true := by decide +kernel
private theorem c1371264 : checkChunk 1371264 128 = true := by decide +kernel
private theorem c1371392 : checkChunk 1371392 128 = true := by decide +kernel
private theorem c1371520 : checkChunk 1371520 128 = true := by decide +kernel
private theorem c1371648 : checkChunk 1371648 128 = true := by decide +kernel
private theorem c1371776 : checkChunk 1371776 128 = true := by decide +kernel
private theorem c1371904 : checkChunk 1371904 128 = true := by decide +kernel
private theorem c1372032 : checkChunk 1372032 128 = true := by decide +kernel
private theorem c1372160 : checkChunk 1372160 128 = true := by decide +kernel
private theorem c1372288 : checkChunk 1372288 128 = true := by decide +kernel
private theorem c1372416 : checkChunk 1372416 128 = true := by decide +kernel
private theorem c1372544 : checkChunk 1372544 128 = true := by decide +kernel
private theorem c1372672 : checkChunk 1372672 128 = true := by decide +kernel
private theorem c1372800 : checkChunk 1372800 128 = true := by decide +kernel
private theorem c1372928 : checkChunk 1372928 128 = true := by decide +kernel
private theorem c1373056 : checkChunk 1373056 128 = true := by decide +kernel
private theorem c1373184 : checkChunk 1373184 128 = true := by decide +kernel
private theorem c1373312 : checkChunk 1373312 128 = true := by decide +kernel
private theorem c1373440 : checkChunk 1373440 128 = true := by decide +kernel
private theorem c1373568 : checkChunk 1373568 128 = true := by decide +kernel
private theorem c1373696 : checkChunk 1373696 128 = true := by decide +kernel
private theorem c1373824 : checkChunk 1373824 128 = true := by decide +kernel
private theorem c1373952 : checkChunk 1373952 128 = true := by decide +kernel
private theorem c1374080 : checkChunk 1374080 128 = true := by decide +kernel
private theorem c1374208 : checkChunk 1374208 128 = true := by decide +kernel
private theorem c1374336 : checkChunk 1374336 128 = true := by decide +kernel
private theorem c1374464 : checkChunk 1374464 128 = true := by decide +kernel
private theorem c1374592 : checkChunk 1374592 128 = true := by decide +kernel
private theorem c1374720 : checkChunk 1374720 128 = true := by decide +kernel
private theorem c1374848 : checkChunk 1374848 128 = true := by decide +kernel
private theorem c1374976 : checkChunk 1374976 128 = true := by decide +kernel
private theorem c1375104 : checkChunk 1375104 128 = true := by decide +kernel
private theorem c1375232 : checkChunk 1375232 128 = true := by decide +kernel
private theorem c1375360 : checkChunk 1375360 128 = true := by decide +kernel
private theorem c1375488 : checkChunk 1375488 128 = true := by decide +kernel
private theorem c1375616 : checkChunk 1375616 128 = true := by decide +kernel
private theorem c1375744 : checkChunk 1375744 128 = true := by decide +kernel
private theorem c1375872 : checkChunk 1375872 128 = true := by decide +kernel
private theorem c1376000 : checkChunk 1376000 128 = true := by decide +kernel
private theorem c1376128 : checkChunk 1376128 128 = true := by decide +kernel

public theorem checked : Checked 1368064 1376256 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1368064 128 c1368064) (checkChunk_sound 1368192 128 c1368192)) (Checked.append (checkChunk_sound 1368320 128 c1368320) (checkChunk_sound 1368448 128 c1368448))) (Checked.append (Checked.append (checkChunk_sound 1368576 128 c1368576) (checkChunk_sound 1368704 128 c1368704)) (Checked.append (checkChunk_sound 1368832 128 c1368832) (checkChunk_sound 1368960 128 c1368960)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1369088 128 c1369088) (checkChunk_sound 1369216 128 c1369216)) (Checked.append (checkChunk_sound 1369344 128 c1369344) (checkChunk_sound 1369472 128 c1369472))) (Checked.append (Checked.append (checkChunk_sound 1369600 128 c1369600) (checkChunk_sound 1369728 128 c1369728)) (Checked.append (checkChunk_sound 1369856 128 c1369856) (checkChunk_sound 1369984 128 c1369984))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1370112 128 c1370112) (checkChunk_sound 1370240 128 c1370240)) (Checked.append (checkChunk_sound 1370368 128 c1370368) (checkChunk_sound 1370496 128 c1370496))) (Checked.append (Checked.append (checkChunk_sound 1370624 128 c1370624) (checkChunk_sound 1370752 128 c1370752)) (Checked.append (checkChunk_sound 1370880 128 c1370880) (checkChunk_sound 1371008 128 c1371008)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1371136 128 c1371136) (checkChunk_sound 1371264 128 c1371264)) (Checked.append (checkChunk_sound 1371392 128 c1371392) (checkChunk_sound 1371520 128 c1371520))) (Checked.append (Checked.append (checkChunk_sound 1371648 128 c1371648) (checkChunk_sound 1371776 128 c1371776)) (Checked.append (checkChunk_sound 1371904 128 c1371904) (checkChunk_sound 1372032 128 c1372032)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1372160 128 c1372160) (checkChunk_sound 1372288 128 c1372288)) (Checked.append (checkChunk_sound 1372416 128 c1372416) (checkChunk_sound 1372544 128 c1372544))) (Checked.append (Checked.append (checkChunk_sound 1372672 128 c1372672) (checkChunk_sound 1372800 128 c1372800)) (Checked.append (checkChunk_sound 1372928 128 c1372928) (checkChunk_sound 1373056 128 c1373056)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1373184 128 c1373184) (checkChunk_sound 1373312 128 c1373312)) (Checked.append (checkChunk_sound 1373440 128 c1373440) (checkChunk_sound 1373568 128 c1373568))) (Checked.append (Checked.append (checkChunk_sound 1373696 128 c1373696) (checkChunk_sound 1373824 128 c1373824)) (Checked.append (checkChunk_sound 1373952 128 c1373952) (checkChunk_sound 1374080 128 c1374080))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1374208 128 c1374208) (checkChunk_sound 1374336 128 c1374336)) (Checked.append (checkChunk_sound 1374464 128 c1374464) (checkChunk_sound 1374592 128 c1374592))) (Checked.append (Checked.append (checkChunk_sound 1374720 128 c1374720) (checkChunk_sound 1374848 128 c1374848)) (Checked.append (checkChunk_sound 1374976 128 c1374976) (checkChunk_sound 1375104 128 c1375104)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1375232 128 c1375232) (checkChunk_sound 1375360 128 c1375360)) (Checked.append (checkChunk_sound 1375488 128 c1375488) (checkChunk_sound 1375616 128 c1375616))) (Checked.append (Checked.append (checkChunk_sound 1375744 128 c1375744) (checkChunk_sound 1375872 128 c1375872)) (Checked.append (checkChunk_sound 1376000 128 c1376000) (checkChunk_sound 1376128 128 c1376128)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B010
