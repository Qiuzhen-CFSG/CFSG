module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1400832, 1409024).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B014
private theorem c1400832 : checkChunk 1400832 128 = true := by decide +kernel
private theorem c1400960 : checkChunk 1400960 128 = true := by decide +kernel
private theorem c1401088 : checkChunk 1401088 128 = true := by decide +kernel
private theorem c1401216 : checkChunk 1401216 128 = true := by decide +kernel
private theorem c1401344 : checkChunk 1401344 128 = true := by decide +kernel
private theorem c1401472 : checkChunk 1401472 128 = true := by decide +kernel
private theorem c1401600 : checkChunk 1401600 128 = true := by decide +kernel
private theorem c1401728 : checkChunk 1401728 128 = true := by decide +kernel
private theorem c1401856 : checkChunk 1401856 128 = true := by decide +kernel
private theorem c1401984 : checkChunk 1401984 128 = true := by decide +kernel
private theorem c1402112 : checkChunk 1402112 128 = true := by decide +kernel
private theorem c1402240 : checkChunk 1402240 128 = true := by decide +kernel
private theorem c1402368 : checkChunk 1402368 128 = true := by decide +kernel
private theorem c1402496 : checkChunk 1402496 128 = true := by decide +kernel
private theorem c1402624 : checkChunk 1402624 128 = true := by decide +kernel
private theorem c1402752 : checkChunk 1402752 128 = true := by decide +kernel
private theorem c1402880 : checkChunk 1402880 128 = true := by decide +kernel
private theorem c1403008 : checkChunk 1403008 128 = true := by decide +kernel
private theorem c1403136 : checkChunk 1403136 128 = true := by decide +kernel
private theorem c1403264 : checkChunk 1403264 128 = true := by decide +kernel
private theorem c1403392 : checkChunk 1403392 128 = true := by decide +kernel
private theorem c1403520 : checkChunk 1403520 128 = true := by decide +kernel
private theorem c1403648 : checkChunk 1403648 128 = true := by decide +kernel
private theorem c1403776 : checkChunk 1403776 128 = true := by decide +kernel
private theorem c1403904 : checkChunk 1403904 128 = true := by decide +kernel
private theorem c1404032 : checkChunk 1404032 128 = true := by decide +kernel
private theorem c1404160 : checkChunk 1404160 128 = true := by decide +kernel
private theorem c1404288 : checkChunk 1404288 128 = true := by decide +kernel
private theorem c1404416 : checkChunk 1404416 128 = true := by decide +kernel
private theorem c1404544 : checkChunk 1404544 128 = true := by decide +kernel
private theorem c1404672 : checkChunk 1404672 128 = true := by decide +kernel
private theorem c1404800 : checkChunk 1404800 128 = true := by decide +kernel
private theorem c1404928 : checkChunk 1404928 128 = true := by decide +kernel
private theorem c1405056 : checkChunk 1405056 128 = true := by decide +kernel
private theorem c1405184 : checkChunk 1405184 128 = true := by decide +kernel
private theorem c1405312 : checkChunk 1405312 128 = true := by decide +kernel
private theorem c1405440 : checkChunk 1405440 128 = true := by decide +kernel
private theorem c1405568 : checkChunk 1405568 128 = true := by decide +kernel
private theorem c1405696 : checkChunk 1405696 128 = true := by decide +kernel
private theorem c1405824 : checkChunk 1405824 128 = true := by decide +kernel
private theorem c1405952 : checkChunk 1405952 128 = true := by decide +kernel
private theorem c1406080 : checkChunk 1406080 128 = true := by decide +kernel
private theorem c1406208 : checkChunk 1406208 128 = true := by decide +kernel
private theorem c1406336 : checkChunk 1406336 128 = true := by decide +kernel
private theorem c1406464 : checkChunk 1406464 128 = true := by decide +kernel
private theorem c1406592 : checkChunk 1406592 128 = true := by decide +kernel
private theorem c1406720 : checkChunk 1406720 128 = true := by decide +kernel
private theorem c1406848 : checkChunk 1406848 128 = true := by decide +kernel
private theorem c1406976 : checkChunk 1406976 128 = true := by decide +kernel
private theorem c1407104 : checkChunk 1407104 128 = true := by decide +kernel
private theorem c1407232 : checkChunk 1407232 128 = true := by decide +kernel
private theorem c1407360 : checkChunk 1407360 128 = true := by decide +kernel
private theorem c1407488 : checkChunk 1407488 128 = true := by decide +kernel
private theorem c1407616 : checkChunk 1407616 128 = true := by decide +kernel
private theorem c1407744 : checkChunk 1407744 128 = true := by decide +kernel
private theorem c1407872 : checkChunk 1407872 128 = true := by decide +kernel
private theorem c1408000 : checkChunk 1408000 128 = true := by decide +kernel
private theorem c1408128 : checkChunk 1408128 128 = true := by decide +kernel
private theorem c1408256 : checkChunk 1408256 128 = true := by decide +kernel
private theorem c1408384 : checkChunk 1408384 128 = true := by decide +kernel
private theorem c1408512 : checkChunk 1408512 128 = true := by decide +kernel
private theorem c1408640 : checkChunk 1408640 128 = true := by decide +kernel
private theorem c1408768 : checkChunk 1408768 128 = true := by decide +kernel
private theorem c1408896 : checkChunk 1408896 128 = true := by decide +kernel

public theorem checked : Checked 1400832 1409024 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1400832 128 c1400832) (checkChunk_sound 1400960 128 c1400960)) (Checked.append (checkChunk_sound 1401088 128 c1401088) (checkChunk_sound 1401216 128 c1401216))) (Checked.append (Checked.append (checkChunk_sound 1401344 128 c1401344) (checkChunk_sound 1401472 128 c1401472)) (Checked.append (checkChunk_sound 1401600 128 c1401600) (checkChunk_sound 1401728 128 c1401728)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1401856 128 c1401856) (checkChunk_sound 1401984 128 c1401984)) (Checked.append (checkChunk_sound 1402112 128 c1402112) (checkChunk_sound 1402240 128 c1402240))) (Checked.append (Checked.append (checkChunk_sound 1402368 128 c1402368) (checkChunk_sound 1402496 128 c1402496)) (Checked.append (checkChunk_sound 1402624 128 c1402624) (checkChunk_sound 1402752 128 c1402752))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1402880 128 c1402880) (checkChunk_sound 1403008 128 c1403008)) (Checked.append (checkChunk_sound 1403136 128 c1403136) (checkChunk_sound 1403264 128 c1403264))) (Checked.append (Checked.append (checkChunk_sound 1403392 128 c1403392) (checkChunk_sound 1403520 128 c1403520)) (Checked.append (checkChunk_sound 1403648 128 c1403648) (checkChunk_sound 1403776 128 c1403776)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1403904 128 c1403904) (checkChunk_sound 1404032 128 c1404032)) (Checked.append (checkChunk_sound 1404160 128 c1404160) (checkChunk_sound 1404288 128 c1404288))) (Checked.append (Checked.append (checkChunk_sound 1404416 128 c1404416) (checkChunk_sound 1404544 128 c1404544)) (Checked.append (checkChunk_sound 1404672 128 c1404672) (checkChunk_sound 1404800 128 c1404800)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1404928 128 c1404928) (checkChunk_sound 1405056 128 c1405056)) (Checked.append (checkChunk_sound 1405184 128 c1405184) (checkChunk_sound 1405312 128 c1405312))) (Checked.append (Checked.append (checkChunk_sound 1405440 128 c1405440) (checkChunk_sound 1405568 128 c1405568)) (Checked.append (checkChunk_sound 1405696 128 c1405696) (checkChunk_sound 1405824 128 c1405824)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1405952 128 c1405952) (checkChunk_sound 1406080 128 c1406080)) (Checked.append (checkChunk_sound 1406208 128 c1406208) (checkChunk_sound 1406336 128 c1406336))) (Checked.append (Checked.append (checkChunk_sound 1406464 128 c1406464) (checkChunk_sound 1406592 128 c1406592)) (Checked.append (checkChunk_sound 1406720 128 c1406720) (checkChunk_sound 1406848 128 c1406848))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1406976 128 c1406976) (checkChunk_sound 1407104 128 c1407104)) (Checked.append (checkChunk_sound 1407232 128 c1407232) (checkChunk_sound 1407360 128 c1407360))) (Checked.append (Checked.append (checkChunk_sound 1407488 128 c1407488) (checkChunk_sound 1407616 128 c1407616)) (Checked.append (checkChunk_sound 1407744 128 c1407744) (checkChunk_sound 1407872 128 c1407872)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1408000 128 c1408000) (checkChunk_sound 1408128 128 c1408128)) (Checked.append (checkChunk_sound 1408256 128 c1408256) (checkChunk_sound 1408384 128 c1408384))) (Checked.append (Checked.append (checkChunk_sound 1408512 128 c1408512) (checkChunk_sound 1408640 128 c1408640)) (Checked.append (checkChunk_sound 1408768 128 c1408768) (checkChunk_sound 1408896 128 c1408896)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B014
