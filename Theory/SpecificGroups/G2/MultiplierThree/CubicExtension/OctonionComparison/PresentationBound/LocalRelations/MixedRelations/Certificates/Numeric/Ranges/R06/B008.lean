module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1351680, 1359872).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B008
private theorem c1351680 : checkChunk 1351680 128 = true := by decide +kernel
private theorem c1351808 : checkChunk 1351808 128 = true := by decide +kernel
private theorem c1351936 : checkChunk 1351936 128 = true := by decide +kernel
private theorem c1352064 : checkChunk 1352064 128 = true := by decide +kernel
private theorem c1352192 : checkChunk 1352192 128 = true := by decide +kernel
private theorem c1352320 : checkChunk 1352320 128 = true := by decide +kernel
private theorem c1352448 : checkChunk 1352448 128 = true := by decide +kernel
private theorem c1352576 : checkChunk 1352576 128 = true := by decide +kernel
private theorem c1352704 : checkChunk 1352704 128 = true := by decide +kernel
private theorem c1352832 : checkChunk 1352832 128 = true := by decide +kernel
private theorem c1352960 : checkChunk 1352960 128 = true := by decide +kernel
private theorem c1353088 : checkChunk 1353088 128 = true := by decide +kernel
private theorem c1353216 : checkChunk 1353216 128 = true := by decide +kernel
private theorem c1353344 : checkChunk 1353344 128 = true := by decide +kernel
private theorem c1353472 : checkChunk 1353472 128 = true := by decide +kernel
private theorem c1353600 : checkChunk 1353600 128 = true := by decide +kernel
private theorem c1353728 : checkChunk 1353728 128 = true := by decide +kernel
private theorem c1353856 : checkChunk 1353856 128 = true := by decide +kernel
private theorem c1353984 : checkChunk 1353984 128 = true := by decide +kernel
private theorem c1354112 : checkChunk 1354112 128 = true := by decide +kernel
private theorem c1354240 : checkChunk 1354240 128 = true := by decide +kernel
private theorem c1354368 : checkChunk 1354368 128 = true := by decide +kernel
private theorem c1354496 : checkChunk 1354496 128 = true := by decide +kernel
private theorem c1354624 : checkChunk 1354624 128 = true := by decide +kernel
private theorem c1354752 : checkChunk 1354752 128 = true := by decide +kernel
private theorem c1354880 : checkChunk 1354880 128 = true := by decide +kernel
private theorem c1355008 : checkChunk 1355008 128 = true := by decide +kernel
private theorem c1355136 : checkChunk 1355136 128 = true := by decide +kernel
private theorem c1355264 : checkChunk 1355264 128 = true := by decide +kernel
private theorem c1355392 : checkChunk 1355392 128 = true := by decide +kernel
private theorem c1355520 : checkChunk 1355520 128 = true := by decide +kernel
private theorem c1355648 : checkChunk 1355648 128 = true := by decide +kernel
private theorem c1355776 : checkChunk 1355776 128 = true := by decide +kernel
private theorem c1355904 : checkChunk 1355904 128 = true := by decide +kernel
private theorem c1356032 : checkChunk 1356032 128 = true := by decide +kernel
private theorem c1356160 : checkChunk 1356160 128 = true := by decide +kernel
private theorem c1356288 : checkChunk 1356288 128 = true := by decide +kernel
private theorem c1356416 : checkChunk 1356416 128 = true := by decide +kernel
private theorem c1356544 : checkChunk 1356544 128 = true := by decide +kernel
private theorem c1356672 : checkChunk 1356672 128 = true := by decide +kernel
private theorem c1356800 : checkChunk 1356800 128 = true := by decide +kernel
private theorem c1356928 : checkChunk 1356928 128 = true := by decide +kernel
private theorem c1357056 : checkChunk 1357056 128 = true := by decide +kernel
private theorem c1357184 : checkChunk 1357184 128 = true := by decide +kernel
private theorem c1357312 : checkChunk 1357312 128 = true := by decide +kernel
private theorem c1357440 : checkChunk 1357440 128 = true := by decide +kernel
private theorem c1357568 : checkChunk 1357568 128 = true := by decide +kernel
private theorem c1357696 : checkChunk 1357696 128 = true := by decide +kernel
private theorem c1357824 : checkChunk 1357824 128 = true := by decide +kernel
private theorem c1357952 : checkChunk 1357952 128 = true := by decide +kernel
private theorem c1358080 : checkChunk 1358080 128 = true := by decide +kernel
private theorem c1358208 : checkChunk 1358208 128 = true := by decide +kernel
private theorem c1358336 : checkChunk 1358336 128 = true := by decide +kernel
private theorem c1358464 : checkChunk 1358464 128 = true := by decide +kernel
private theorem c1358592 : checkChunk 1358592 128 = true := by decide +kernel
private theorem c1358720 : checkChunk 1358720 128 = true := by decide +kernel
private theorem c1358848 : checkChunk 1358848 128 = true := by decide +kernel
private theorem c1358976 : checkChunk 1358976 128 = true := by decide +kernel
private theorem c1359104 : checkChunk 1359104 128 = true := by decide +kernel
private theorem c1359232 : checkChunk 1359232 128 = true := by decide +kernel
private theorem c1359360 : checkChunk 1359360 128 = true := by decide +kernel
private theorem c1359488 : checkChunk 1359488 128 = true := by decide +kernel
private theorem c1359616 : checkChunk 1359616 128 = true := by decide +kernel
private theorem c1359744 : checkChunk 1359744 128 = true := by decide +kernel

public theorem checked : Checked 1351680 1359872 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1351680 128 c1351680) (checkChunk_sound 1351808 128 c1351808)) (Checked.append (checkChunk_sound 1351936 128 c1351936) (checkChunk_sound 1352064 128 c1352064))) (Checked.append (Checked.append (checkChunk_sound 1352192 128 c1352192) (checkChunk_sound 1352320 128 c1352320)) (Checked.append (checkChunk_sound 1352448 128 c1352448) (checkChunk_sound 1352576 128 c1352576)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1352704 128 c1352704) (checkChunk_sound 1352832 128 c1352832)) (Checked.append (checkChunk_sound 1352960 128 c1352960) (checkChunk_sound 1353088 128 c1353088))) (Checked.append (Checked.append (checkChunk_sound 1353216 128 c1353216) (checkChunk_sound 1353344 128 c1353344)) (Checked.append (checkChunk_sound 1353472 128 c1353472) (checkChunk_sound 1353600 128 c1353600))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1353728 128 c1353728) (checkChunk_sound 1353856 128 c1353856)) (Checked.append (checkChunk_sound 1353984 128 c1353984) (checkChunk_sound 1354112 128 c1354112))) (Checked.append (Checked.append (checkChunk_sound 1354240 128 c1354240) (checkChunk_sound 1354368 128 c1354368)) (Checked.append (checkChunk_sound 1354496 128 c1354496) (checkChunk_sound 1354624 128 c1354624)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1354752 128 c1354752) (checkChunk_sound 1354880 128 c1354880)) (Checked.append (checkChunk_sound 1355008 128 c1355008) (checkChunk_sound 1355136 128 c1355136))) (Checked.append (Checked.append (checkChunk_sound 1355264 128 c1355264) (checkChunk_sound 1355392 128 c1355392)) (Checked.append (checkChunk_sound 1355520 128 c1355520) (checkChunk_sound 1355648 128 c1355648)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1355776 128 c1355776) (checkChunk_sound 1355904 128 c1355904)) (Checked.append (checkChunk_sound 1356032 128 c1356032) (checkChunk_sound 1356160 128 c1356160))) (Checked.append (Checked.append (checkChunk_sound 1356288 128 c1356288) (checkChunk_sound 1356416 128 c1356416)) (Checked.append (checkChunk_sound 1356544 128 c1356544) (checkChunk_sound 1356672 128 c1356672)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1356800 128 c1356800) (checkChunk_sound 1356928 128 c1356928)) (Checked.append (checkChunk_sound 1357056 128 c1357056) (checkChunk_sound 1357184 128 c1357184))) (Checked.append (Checked.append (checkChunk_sound 1357312 128 c1357312) (checkChunk_sound 1357440 128 c1357440)) (Checked.append (checkChunk_sound 1357568 128 c1357568) (checkChunk_sound 1357696 128 c1357696))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1357824 128 c1357824) (checkChunk_sound 1357952 128 c1357952)) (Checked.append (checkChunk_sound 1358080 128 c1358080) (checkChunk_sound 1358208 128 c1358208))) (Checked.append (Checked.append (checkChunk_sound 1358336 128 c1358336) (checkChunk_sound 1358464 128 c1358464)) (Checked.append (checkChunk_sound 1358592 128 c1358592) (checkChunk_sound 1358720 128 c1358720)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1358848 128 c1358848) (checkChunk_sound 1358976 128 c1358976)) (Checked.append (checkChunk_sound 1359104 128 c1359104) (checkChunk_sound 1359232 128 c1359232))) (Checked.append (Checked.append (checkChunk_sound 1359360 128 c1359360) (checkChunk_sound 1359488 128 c1359488)) (Checked.append (checkChunk_sound 1359616 128 c1359616) (checkChunk_sound 1359744 128 c1359744)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B008
