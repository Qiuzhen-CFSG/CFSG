module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1589248, 1597440).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B011
private theorem c1589248 : checkChunk 1589248 128 = true := by decide +kernel
private theorem c1589376 : checkChunk 1589376 128 = true := by decide +kernel
private theorem c1589504 : checkChunk 1589504 128 = true := by decide +kernel
private theorem c1589632 : checkChunk 1589632 128 = true := by decide +kernel
private theorem c1589760 : checkChunk 1589760 128 = true := by decide +kernel
private theorem c1589888 : checkChunk 1589888 128 = true := by decide +kernel
private theorem c1590016 : checkChunk 1590016 128 = true := by decide +kernel
private theorem c1590144 : checkChunk 1590144 128 = true := by decide +kernel
private theorem c1590272 : checkChunk 1590272 128 = true := by decide +kernel
private theorem c1590400 : checkChunk 1590400 128 = true := by decide +kernel
private theorem c1590528 : checkChunk 1590528 128 = true := by decide +kernel
private theorem c1590656 : checkChunk 1590656 128 = true := by decide +kernel
private theorem c1590784 : checkChunk 1590784 128 = true := by decide +kernel
private theorem c1590912 : checkChunk 1590912 128 = true := by decide +kernel
private theorem c1591040 : checkChunk 1591040 128 = true := by decide +kernel
private theorem c1591168 : checkChunk 1591168 128 = true := by decide +kernel
private theorem c1591296 : checkChunk 1591296 128 = true := by decide +kernel
private theorem c1591424 : checkChunk 1591424 128 = true := by decide +kernel
private theorem c1591552 : checkChunk 1591552 128 = true := by decide +kernel
private theorem c1591680 : checkChunk 1591680 128 = true := by decide +kernel
private theorem c1591808 : checkChunk 1591808 128 = true := by decide +kernel
private theorem c1591936 : checkChunk 1591936 128 = true := by decide +kernel
private theorem c1592064 : checkChunk 1592064 128 = true := by decide +kernel
private theorem c1592192 : checkChunk 1592192 128 = true := by decide +kernel
private theorem c1592320 : checkChunk 1592320 128 = true := by decide +kernel
private theorem c1592448 : checkChunk 1592448 128 = true := by decide +kernel
private theorem c1592576 : checkChunk 1592576 128 = true := by decide +kernel
private theorem c1592704 : checkChunk 1592704 128 = true := by decide +kernel
private theorem c1592832 : checkChunk 1592832 128 = true := by decide +kernel
private theorem c1592960 : checkChunk 1592960 128 = true := by decide +kernel
private theorem c1593088 : checkChunk 1593088 128 = true := by decide +kernel
private theorem c1593216 : checkChunk 1593216 128 = true := by decide +kernel
private theorem c1593344 : checkChunk 1593344 128 = true := by decide +kernel
private theorem c1593472 : checkChunk 1593472 128 = true := by decide +kernel
private theorem c1593600 : checkChunk 1593600 128 = true := by decide +kernel
private theorem c1593728 : checkChunk 1593728 128 = true := by decide +kernel
private theorem c1593856 : checkChunk 1593856 128 = true := by decide +kernel
private theorem c1593984 : checkChunk 1593984 128 = true := by decide +kernel
private theorem c1594112 : checkChunk 1594112 128 = true := by decide +kernel
private theorem c1594240 : checkChunk 1594240 128 = true := by decide +kernel
private theorem c1594368 : checkChunk 1594368 128 = true := by decide +kernel
private theorem c1594496 : checkChunk 1594496 128 = true := by decide +kernel
private theorem c1594624 : checkChunk 1594624 128 = true := by decide +kernel
private theorem c1594752 : checkChunk 1594752 128 = true := by decide +kernel
private theorem c1594880 : checkChunk 1594880 128 = true := by decide +kernel
private theorem c1595008 : checkChunk 1595008 128 = true := by decide +kernel
private theorem c1595136 : checkChunk 1595136 128 = true := by decide +kernel
private theorem c1595264 : checkChunk 1595264 128 = true := by decide +kernel
private theorem c1595392 : checkChunk 1595392 128 = true := by decide +kernel
private theorem c1595520 : checkChunk 1595520 128 = true := by decide +kernel
private theorem c1595648 : checkChunk 1595648 128 = true := by decide +kernel
private theorem c1595776 : checkChunk 1595776 128 = true := by decide +kernel
private theorem c1595904 : checkChunk 1595904 128 = true := by decide +kernel
private theorem c1596032 : checkChunk 1596032 128 = true := by decide +kernel
private theorem c1596160 : checkChunk 1596160 128 = true := by decide +kernel
private theorem c1596288 : checkChunk 1596288 128 = true := by decide +kernel
private theorem c1596416 : checkChunk 1596416 128 = true := by decide +kernel
private theorem c1596544 : checkChunk 1596544 128 = true := by decide +kernel
private theorem c1596672 : checkChunk 1596672 128 = true := by decide +kernel
private theorem c1596800 : checkChunk 1596800 128 = true := by decide +kernel
private theorem c1596928 : checkChunk 1596928 128 = true := by decide +kernel
private theorem c1597056 : checkChunk 1597056 128 = true := by decide +kernel
private theorem c1597184 : checkChunk 1597184 128 = true := by decide +kernel
private theorem c1597312 : checkChunk 1597312 128 = true := by decide +kernel

public theorem checked : Checked 1589248 1597440 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1589248 128 c1589248) (checkChunk_sound 1589376 128 c1589376)) (Checked.append (checkChunk_sound 1589504 128 c1589504) (checkChunk_sound 1589632 128 c1589632))) (Checked.append (Checked.append (checkChunk_sound 1589760 128 c1589760) (checkChunk_sound 1589888 128 c1589888)) (Checked.append (checkChunk_sound 1590016 128 c1590016) (checkChunk_sound 1590144 128 c1590144)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1590272 128 c1590272) (checkChunk_sound 1590400 128 c1590400)) (Checked.append (checkChunk_sound 1590528 128 c1590528) (checkChunk_sound 1590656 128 c1590656))) (Checked.append (Checked.append (checkChunk_sound 1590784 128 c1590784) (checkChunk_sound 1590912 128 c1590912)) (Checked.append (checkChunk_sound 1591040 128 c1591040) (checkChunk_sound 1591168 128 c1591168))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1591296 128 c1591296) (checkChunk_sound 1591424 128 c1591424)) (Checked.append (checkChunk_sound 1591552 128 c1591552) (checkChunk_sound 1591680 128 c1591680))) (Checked.append (Checked.append (checkChunk_sound 1591808 128 c1591808) (checkChunk_sound 1591936 128 c1591936)) (Checked.append (checkChunk_sound 1592064 128 c1592064) (checkChunk_sound 1592192 128 c1592192)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1592320 128 c1592320) (checkChunk_sound 1592448 128 c1592448)) (Checked.append (checkChunk_sound 1592576 128 c1592576) (checkChunk_sound 1592704 128 c1592704))) (Checked.append (Checked.append (checkChunk_sound 1592832 128 c1592832) (checkChunk_sound 1592960 128 c1592960)) (Checked.append (checkChunk_sound 1593088 128 c1593088) (checkChunk_sound 1593216 128 c1593216)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1593344 128 c1593344) (checkChunk_sound 1593472 128 c1593472)) (Checked.append (checkChunk_sound 1593600 128 c1593600) (checkChunk_sound 1593728 128 c1593728))) (Checked.append (Checked.append (checkChunk_sound 1593856 128 c1593856) (checkChunk_sound 1593984 128 c1593984)) (Checked.append (checkChunk_sound 1594112 128 c1594112) (checkChunk_sound 1594240 128 c1594240)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1594368 128 c1594368) (checkChunk_sound 1594496 128 c1594496)) (Checked.append (checkChunk_sound 1594624 128 c1594624) (checkChunk_sound 1594752 128 c1594752))) (Checked.append (Checked.append (checkChunk_sound 1594880 128 c1594880) (checkChunk_sound 1595008 128 c1595008)) (Checked.append (checkChunk_sound 1595136 128 c1595136) (checkChunk_sound 1595264 128 c1595264))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1595392 128 c1595392) (checkChunk_sound 1595520 128 c1595520)) (Checked.append (checkChunk_sound 1595648 128 c1595648) (checkChunk_sound 1595776 128 c1595776))) (Checked.append (Checked.append (checkChunk_sound 1595904 128 c1595904) (checkChunk_sound 1596032 128 c1596032)) (Checked.append (checkChunk_sound 1596160 128 c1596160) (checkChunk_sound 1596288 128 c1596288)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1596416 128 c1596416) (checkChunk_sound 1596544 128 c1596544)) (Checked.append (checkChunk_sound 1596672 128 c1596672) (checkChunk_sound 1596800 128 c1596800))) (Checked.append (Checked.append (checkChunk_sound 1596928 128 c1596928) (checkChunk_sound 1597056 128 c1597056)) (Checked.append (checkChunk_sound 1597184 128 c1597184) (checkChunk_sound 1597312 128 c1597312)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B011
