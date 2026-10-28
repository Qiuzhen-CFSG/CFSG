module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1572864, 1581056).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B009
private theorem c1572864 : checkChunk 1572864 128 = true := by decide +kernel
private theorem c1572992 : checkChunk 1572992 128 = true := by decide +kernel
private theorem c1573120 : checkChunk 1573120 128 = true := by decide +kernel
private theorem c1573248 : checkChunk 1573248 128 = true := by decide +kernel
private theorem c1573376 : checkChunk 1573376 128 = true := by decide +kernel
private theorem c1573504 : checkChunk 1573504 128 = true := by decide +kernel
private theorem c1573632 : checkChunk 1573632 128 = true := by decide +kernel
private theorem c1573760 : checkChunk 1573760 128 = true := by decide +kernel
private theorem c1573888 : checkChunk 1573888 128 = true := by decide +kernel
private theorem c1574016 : checkChunk 1574016 128 = true := by decide +kernel
private theorem c1574144 : checkChunk 1574144 128 = true := by decide +kernel
private theorem c1574272 : checkChunk 1574272 128 = true := by decide +kernel
private theorem c1574400 : checkChunk 1574400 128 = true := by decide +kernel
private theorem c1574528 : checkChunk 1574528 128 = true := by decide +kernel
private theorem c1574656 : checkChunk 1574656 128 = true := by decide +kernel
private theorem c1574784 : checkChunk 1574784 128 = true := by decide +kernel
private theorem c1574912 : checkChunk 1574912 128 = true := by decide +kernel
private theorem c1575040 : checkChunk 1575040 128 = true := by decide +kernel
private theorem c1575168 : checkChunk 1575168 128 = true := by decide +kernel
private theorem c1575296 : checkChunk 1575296 128 = true := by decide +kernel
private theorem c1575424 : checkChunk 1575424 128 = true := by decide +kernel
private theorem c1575552 : checkChunk 1575552 128 = true := by decide +kernel
private theorem c1575680 : checkChunk 1575680 128 = true := by decide +kernel
private theorem c1575808 : checkChunk 1575808 128 = true := by decide +kernel
private theorem c1575936 : checkChunk 1575936 128 = true := by decide +kernel
private theorem c1576064 : checkChunk 1576064 128 = true := by decide +kernel
private theorem c1576192 : checkChunk 1576192 128 = true := by decide +kernel
private theorem c1576320 : checkChunk 1576320 128 = true := by decide +kernel
private theorem c1576448 : checkChunk 1576448 128 = true := by decide +kernel
private theorem c1576576 : checkChunk 1576576 128 = true := by decide +kernel
private theorem c1576704 : checkChunk 1576704 128 = true := by decide +kernel
private theorem c1576832 : checkChunk 1576832 128 = true := by decide +kernel
private theorem c1576960 : checkChunk 1576960 128 = true := by decide +kernel
private theorem c1577088 : checkChunk 1577088 128 = true := by decide +kernel
private theorem c1577216 : checkChunk 1577216 128 = true := by decide +kernel
private theorem c1577344 : checkChunk 1577344 128 = true := by decide +kernel
private theorem c1577472 : checkChunk 1577472 128 = true := by decide +kernel
private theorem c1577600 : checkChunk 1577600 128 = true := by decide +kernel
private theorem c1577728 : checkChunk 1577728 128 = true := by decide +kernel
private theorem c1577856 : checkChunk 1577856 128 = true := by decide +kernel
private theorem c1577984 : checkChunk 1577984 128 = true := by decide +kernel
private theorem c1578112 : checkChunk 1578112 128 = true := by decide +kernel
private theorem c1578240 : checkChunk 1578240 128 = true := by decide +kernel
private theorem c1578368 : checkChunk 1578368 128 = true := by decide +kernel
private theorem c1578496 : checkChunk 1578496 128 = true := by decide +kernel
private theorem c1578624 : checkChunk 1578624 128 = true := by decide +kernel
private theorem c1578752 : checkChunk 1578752 128 = true := by decide +kernel
private theorem c1578880 : checkChunk 1578880 128 = true := by decide +kernel
private theorem c1579008 : checkChunk 1579008 128 = true := by decide +kernel
private theorem c1579136 : checkChunk 1579136 128 = true := by decide +kernel
private theorem c1579264 : checkChunk 1579264 128 = true := by decide +kernel
private theorem c1579392 : checkChunk 1579392 128 = true := by decide +kernel
private theorem c1579520 : checkChunk 1579520 128 = true := by decide +kernel
private theorem c1579648 : checkChunk 1579648 128 = true := by decide +kernel
private theorem c1579776 : checkChunk 1579776 128 = true := by decide +kernel
private theorem c1579904 : checkChunk 1579904 128 = true := by decide +kernel
private theorem c1580032 : checkChunk 1580032 128 = true := by decide +kernel
private theorem c1580160 : checkChunk 1580160 128 = true := by decide +kernel
private theorem c1580288 : checkChunk 1580288 128 = true := by decide +kernel
private theorem c1580416 : checkChunk 1580416 128 = true := by decide +kernel
private theorem c1580544 : checkChunk 1580544 128 = true := by decide +kernel
private theorem c1580672 : checkChunk 1580672 128 = true := by decide +kernel
private theorem c1580800 : checkChunk 1580800 128 = true := by decide +kernel
private theorem c1580928 : checkChunk 1580928 128 = true := by decide +kernel

public theorem checked : Checked 1572864 1581056 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1572864 128 c1572864) (checkChunk_sound 1572992 128 c1572992)) (Checked.append (checkChunk_sound 1573120 128 c1573120) (checkChunk_sound 1573248 128 c1573248))) (Checked.append (Checked.append (checkChunk_sound 1573376 128 c1573376) (checkChunk_sound 1573504 128 c1573504)) (Checked.append (checkChunk_sound 1573632 128 c1573632) (checkChunk_sound 1573760 128 c1573760)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1573888 128 c1573888) (checkChunk_sound 1574016 128 c1574016)) (Checked.append (checkChunk_sound 1574144 128 c1574144) (checkChunk_sound 1574272 128 c1574272))) (Checked.append (Checked.append (checkChunk_sound 1574400 128 c1574400) (checkChunk_sound 1574528 128 c1574528)) (Checked.append (checkChunk_sound 1574656 128 c1574656) (checkChunk_sound 1574784 128 c1574784))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1574912 128 c1574912) (checkChunk_sound 1575040 128 c1575040)) (Checked.append (checkChunk_sound 1575168 128 c1575168) (checkChunk_sound 1575296 128 c1575296))) (Checked.append (Checked.append (checkChunk_sound 1575424 128 c1575424) (checkChunk_sound 1575552 128 c1575552)) (Checked.append (checkChunk_sound 1575680 128 c1575680) (checkChunk_sound 1575808 128 c1575808)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1575936 128 c1575936) (checkChunk_sound 1576064 128 c1576064)) (Checked.append (checkChunk_sound 1576192 128 c1576192) (checkChunk_sound 1576320 128 c1576320))) (Checked.append (Checked.append (checkChunk_sound 1576448 128 c1576448) (checkChunk_sound 1576576 128 c1576576)) (Checked.append (checkChunk_sound 1576704 128 c1576704) (checkChunk_sound 1576832 128 c1576832)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1576960 128 c1576960) (checkChunk_sound 1577088 128 c1577088)) (Checked.append (checkChunk_sound 1577216 128 c1577216) (checkChunk_sound 1577344 128 c1577344))) (Checked.append (Checked.append (checkChunk_sound 1577472 128 c1577472) (checkChunk_sound 1577600 128 c1577600)) (Checked.append (checkChunk_sound 1577728 128 c1577728) (checkChunk_sound 1577856 128 c1577856)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1577984 128 c1577984) (checkChunk_sound 1578112 128 c1578112)) (Checked.append (checkChunk_sound 1578240 128 c1578240) (checkChunk_sound 1578368 128 c1578368))) (Checked.append (Checked.append (checkChunk_sound 1578496 128 c1578496) (checkChunk_sound 1578624 128 c1578624)) (Checked.append (checkChunk_sound 1578752 128 c1578752) (checkChunk_sound 1578880 128 c1578880))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1579008 128 c1579008) (checkChunk_sound 1579136 128 c1579136)) (Checked.append (checkChunk_sound 1579264 128 c1579264) (checkChunk_sound 1579392 128 c1579392))) (Checked.append (Checked.append (checkChunk_sound 1579520 128 c1579520) (checkChunk_sound 1579648 128 c1579648)) (Checked.append (checkChunk_sound 1579776 128 c1579776) (checkChunk_sound 1579904 128 c1579904)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1580032 128 c1580032) (checkChunk_sound 1580160 128 c1580160)) (Checked.append (checkChunk_sound 1580288 128 c1580288) (checkChunk_sound 1580416 128 c1580416))) (Checked.append (Checked.append (checkChunk_sound 1580544 128 c1580544) (checkChunk_sound 1580672 128 c1580672)) (Checked.append (checkChunk_sound 1580800 128 c1580800) (checkChunk_sound 1580928 128 c1580928)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B009
