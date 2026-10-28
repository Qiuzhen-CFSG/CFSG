module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1417216, 1425408).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B016
private theorem c1417216 : checkChunk 1417216 128 = true := by decide +kernel
private theorem c1417344 : checkChunk 1417344 128 = true := by decide +kernel
private theorem c1417472 : checkChunk 1417472 128 = true := by decide +kernel
private theorem c1417600 : checkChunk 1417600 128 = true := by decide +kernel
private theorem c1417728 : checkChunk 1417728 128 = true := by decide +kernel
private theorem c1417856 : checkChunk 1417856 128 = true := by decide +kernel
private theorem c1417984 : checkChunk 1417984 128 = true := by decide +kernel
private theorem c1418112 : checkChunk 1418112 128 = true := by decide +kernel
private theorem c1418240 : checkChunk 1418240 128 = true := by decide +kernel
private theorem c1418368 : checkChunk 1418368 128 = true := by decide +kernel
private theorem c1418496 : checkChunk 1418496 128 = true := by decide +kernel
private theorem c1418624 : checkChunk 1418624 128 = true := by decide +kernel
private theorem c1418752 : checkChunk 1418752 128 = true := by decide +kernel
private theorem c1418880 : checkChunk 1418880 128 = true := by decide +kernel
private theorem c1419008 : checkChunk 1419008 128 = true := by decide +kernel
private theorem c1419136 : checkChunk 1419136 128 = true := by decide +kernel
private theorem c1419264 : checkChunk 1419264 128 = true := by decide +kernel
private theorem c1419392 : checkChunk 1419392 128 = true := by decide +kernel
private theorem c1419520 : checkChunk 1419520 128 = true := by decide +kernel
private theorem c1419648 : checkChunk 1419648 128 = true := by decide +kernel
private theorem c1419776 : checkChunk 1419776 128 = true := by decide +kernel
private theorem c1419904 : checkChunk 1419904 128 = true := by decide +kernel
private theorem c1420032 : checkChunk 1420032 128 = true := by decide +kernel
private theorem c1420160 : checkChunk 1420160 128 = true := by decide +kernel
private theorem c1420288 : checkChunk 1420288 128 = true := by decide +kernel
private theorem c1420416 : checkChunk 1420416 128 = true := by decide +kernel
private theorem c1420544 : checkChunk 1420544 128 = true := by decide +kernel
private theorem c1420672 : checkChunk 1420672 128 = true := by decide +kernel
private theorem c1420800 : checkChunk 1420800 128 = true := by decide +kernel
private theorem c1420928 : checkChunk 1420928 128 = true := by decide +kernel
private theorem c1421056 : checkChunk 1421056 128 = true := by decide +kernel
private theorem c1421184 : checkChunk 1421184 128 = true := by decide +kernel
private theorem c1421312 : checkChunk 1421312 128 = true := by decide +kernel
private theorem c1421440 : checkChunk 1421440 128 = true := by decide +kernel
private theorem c1421568 : checkChunk 1421568 128 = true := by decide +kernel
private theorem c1421696 : checkChunk 1421696 128 = true := by decide +kernel
private theorem c1421824 : checkChunk 1421824 128 = true := by decide +kernel
private theorem c1421952 : checkChunk 1421952 128 = true := by decide +kernel
private theorem c1422080 : checkChunk 1422080 128 = true := by decide +kernel
private theorem c1422208 : checkChunk 1422208 128 = true := by decide +kernel
private theorem c1422336 : checkChunk 1422336 128 = true := by decide +kernel
private theorem c1422464 : checkChunk 1422464 128 = true := by decide +kernel
private theorem c1422592 : checkChunk 1422592 128 = true := by decide +kernel
private theorem c1422720 : checkChunk 1422720 128 = true := by decide +kernel
private theorem c1422848 : checkChunk 1422848 128 = true := by decide +kernel
private theorem c1422976 : checkChunk 1422976 128 = true := by decide +kernel
private theorem c1423104 : checkChunk 1423104 128 = true := by decide +kernel
private theorem c1423232 : checkChunk 1423232 128 = true := by decide +kernel
private theorem c1423360 : checkChunk 1423360 128 = true := by decide +kernel
private theorem c1423488 : checkChunk 1423488 128 = true := by decide +kernel
private theorem c1423616 : checkChunk 1423616 128 = true := by decide +kernel
private theorem c1423744 : checkChunk 1423744 128 = true := by decide +kernel
private theorem c1423872 : checkChunk 1423872 128 = true := by decide +kernel
private theorem c1424000 : checkChunk 1424000 128 = true := by decide +kernel
private theorem c1424128 : checkChunk 1424128 128 = true := by decide +kernel
private theorem c1424256 : checkChunk 1424256 128 = true := by decide +kernel
private theorem c1424384 : checkChunk 1424384 128 = true := by decide +kernel
private theorem c1424512 : checkChunk 1424512 128 = true := by decide +kernel
private theorem c1424640 : checkChunk 1424640 128 = true := by decide +kernel
private theorem c1424768 : checkChunk 1424768 128 = true := by decide +kernel
private theorem c1424896 : checkChunk 1424896 128 = true := by decide +kernel
private theorem c1425024 : checkChunk 1425024 128 = true := by decide +kernel
private theorem c1425152 : checkChunk 1425152 128 = true := by decide +kernel
private theorem c1425280 : checkChunk 1425280 128 = true := by decide +kernel

public theorem checked : Checked 1417216 1425408 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1417216 128 c1417216) (checkChunk_sound 1417344 128 c1417344)) (Checked.append (checkChunk_sound 1417472 128 c1417472) (checkChunk_sound 1417600 128 c1417600))) (Checked.append (Checked.append (checkChunk_sound 1417728 128 c1417728) (checkChunk_sound 1417856 128 c1417856)) (Checked.append (checkChunk_sound 1417984 128 c1417984) (checkChunk_sound 1418112 128 c1418112)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1418240 128 c1418240) (checkChunk_sound 1418368 128 c1418368)) (Checked.append (checkChunk_sound 1418496 128 c1418496) (checkChunk_sound 1418624 128 c1418624))) (Checked.append (Checked.append (checkChunk_sound 1418752 128 c1418752) (checkChunk_sound 1418880 128 c1418880)) (Checked.append (checkChunk_sound 1419008 128 c1419008) (checkChunk_sound 1419136 128 c1419136))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1419264 128 c1419264) (checkChunk_sound 1419392 128 c1419392)) (Checked.append (checkChunk_sound 1419520 128 c1419520) (checkChunk_sound 1419648 128 c1419648))) (Checked.append (Checked.append (checkChunk_sound 1419776 128 c1419776) (checkChunk_sound 1419904 128 c1419904)) (Checked.append (checkChunk_sound 1420032 128 c1420032) (checkChunk_sound 1420160 128 c1420160)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1420288 128 c1420288) (checkChunk_sound 1420416 128 c1420416)) (Checked.append (checkChunk_sound 1420544 128 c1420544) (checkChunk_sound 1420672 128 c1420672))) (Checked.append (Checked.append (checkChunk_sound 1420800 128 c1420800) (checkChunk_sound 1420928 128 c1420928)) (Checked.append (checkChunk_sound 1421056 128 c1421056) (checkChunk_sound 1421184 128 c1421184)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1421312 128 c1421312) (checkChunk_sound 1421440 128 c1421440)) (Checked.append (checkChunk_sound 1421568 128 c1421568) (checkChunk_sound 1421696 128 c1421696))) (Checked.append (Checked.append (checkChunk_sound 1421824 128 c1421824) (checkChunk_sound 1421952 128 c1421952)) (Checked.append (checkChunk_sound 1422080 128 c1422080) (checkChunk_sound 1422208 128 c1422208)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1422336 128 c1422336) (checkChunk_sound 1422464 128 c1422464)) (Checked.append (checkChunk_sound 1422592 128 c1422592) (checkChunk_sound 1422720 128 c1422720))) (Checked.append (Checked.append (checkChunk_sound 1422848 128 c1422848) (checkChunk_sound 1422976 128 c1422976)) (Checked.append (checkChunk_sound 1423104 128 c1423104) (checkChunk_sound 1423232 128 c1423232))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1423360 128 c1423360) (checkChunk_sound 1423488 128 c1423488)) (Checked.append (checkChunk_sound 1423616 128 c1423616) (checkChunk_sound 1423744 128 c1423744))) (Checked.append (Checked.append (checkChunk_sound 1423872 128 c1423872) (checkChunk_sound 1424000 128 c1424000)) (Checked.append (checkChunk_sound 1424128 128 c1424128) (checkChunk_sound 1424256 128 c1424256)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1424384 128 c1424384) (checkChunk_sound 1424512 128 c1424512)) (Checked.append (checkChunk_sound 1424640 128 c1424640) (checkChunk_sound 1424768 128 c1424768))) (Checked.append (Checked.append (checkChunk_sound 1424896 128 c1424896) (checkChunk_sound 1425024 128 c1425024)) (Checked.append (checkChunk_sound 1425152 128 c1425152) (checkChunk_sound 1425280 128 c1425280)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B016
