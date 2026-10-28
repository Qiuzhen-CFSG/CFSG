module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1605632, 1613824).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B013
private theorem c1605632 : checkChunk 1605632 128 = true := by decide +kernel
private theorem c1605760 : checkChunk 1605760 128 = true := by decide +kernel
private theorem c1605888 : checkChunk 1605888 128 = true := by decide +kernel
private theorem c1606016 : checkChunk 1606016 128 = true := by decide +kernel
private theorem c1606144 : checkChunk 1606144 128 = true := by decide +kernel
private theorem c1606272 : checkChunk 1606272 128 = true := by decide +kernel
private theorem c1606400 : checkChunk 1606400 128 = true := by decide +kernel
private theorem c1606528 : checkChunk 1606528 128 = true := by decide +kernel
private theorem c1606656 : checkChunk 1606656 128 = true := by decide +kernel
private theorem c1606784 : checkChunk 1606784 128 = true := by decide +kernel
private theorem c1606912 : checkChunk 1606912 128 = true := by decide +kernel
private theorem c1607040 : checkChunk 1607040 128 = true := by decide +kernel
private theorem c1607168 : checkChunk 1607168 128 = true := by decide +kernel
private theorem c1607296 : checkChunk 1607296 128 = true := by decide +kernel
private theorem c1607424 : checkChunk 1607424 128 = true := by decide +kernel
private theorem c1607552 : checkChunk 1607552 128 = true := by decide +kernel
private theorem c1607680 : checkChunk 1607680 128 = true := by decide +kernel
private theorem c1607808 : checkChunk 1607808 128 = true := by decide +kernel
private theorem c1607936 : checkChunk 1607936 128 = true := by decide +kernel
private theorem c1608064 : checkChunk 1608064 128 = true := by decide +kernel
private theorem c1608192 : checkChunk 1608192 128 = true := by decide +kernel
private theorem c1608320 : checkChunk 1608320 128 = true := by decide +kernel
private theorem c1608448 : checkChunk 1608448 128 = true := by decide +kernel
private theorem c1608576 : checkChunk 1608576 128 = true := by decide +kernel
private theorem c1608704 : checkChunk 1608704 128 = true := by decide +kernel
private theorem c1608832 : checkChunk 1608832 128 = true := by decide +kernel
private theorem c1608960 : checkChunk 1608960 128 = true := by decide +kernel
private theorem c1609088 : checkChunk 1609088 128 = true := by decide +kernel
private theorem c1609216 : checkChunk 1609216 128 = true := by decide +kernel
private theorem c1609344 : checkChunk 1609344 128 = true := by decide +kernel
private theorem c1609472 : checkChunk 1609472 128 = true := by decide +kernel
private theorem c1609600 : checkChunk 1609600 128 = true := by decide +kernel
private theorem c1609728 : checkChunk 1609728 128 = true := by decide +kernel
private theorem c1609856 : checkChunk 1609856 128 = true := by decide +kernel
private theorem c1609984 : checkChunk 1609984 128 = true := by decide +kernel
private theorem c1610112 : checkChunk 1610112 128 = true := by decide +kernel
private theorem c1610240 : checkChunk 1610240 128 = true := by decide +kernel
private theorem c1610368 : checkChunk 1610368 128 = true := by decide +kernel
private theorem c1610496 : checkChunk 1610496 128 = true := by decide +kernel
private theorem c1610624 : checkChunk 1610624 128 = true := by decide +kernel
private theorem c1610752 : checkChunk 1610752 128 = true := by decide +kernel
private theorem c1610880 : checkChunk 1610880 128 = true := by decide +kernel
private theorem c1611008 : checkChunk 1611008 128 = true := by decide +kernel
private theorem c1611136 : checkChunk 1611136 128 = true := by decide +kernel
private theorem c1611264 : checkChunk 1611264 128 = true := by decide +kernel
private theorem c1611392 : checkChunk 1611392 128 = true := by decide +kernel
private theorem c1611520 : checkChunk 1611520 128 = true := by decide +kernel
private theorem c1611648 : checkChunk 1611648 128 = true := by decide +kernel
private theorem c1611776 : checkChunk 1611776 128 = true := by decide +kernel
private theorem c1611904 : checkChunk 1611904 128 = true := by decide +kernel
private theorem c1612032 : checkChunk 1612032 128 = true := by decide +kernel
private theorem c1612160 : checkChunk 1612160 128 = true := by decide +kernel
private theorem c1612288 : checkChunk 1612288 128 = true := by decide +kernel
private theorem c1612416 : checkChunk 1612416 128 = true := by decide +kernel
private theorem c1612544 : checkChunk 1612544 128 = true := by decide +kernel
private theorem c1612672 : checkChunk 1612672 128 = true := by decide +kernel
private theorem c1612800 : checkChunk 1612800 128 = true := by decide +kernel
private theorem c1612928 : checkChunk 1612928 128 = true := by decide +kernel
private theorem c1613056 : checkChunk 1613056 128 = true := by decide +kernel
private theorem c1613184 : checkChunk 1613184 128 = true := by decide +kernel
private theorem c1613312 : checkChunk 1613312 128 = true := by decide +kernel
private theorem c1613440 : checkChunk 1613440 128 = true := by decide +kernel
private theorem c1613568 : checkChunk 1613568 128 = true := by decide +kernel
private theorem c1613696 : checkChunk 1613696 128 = true := by decide +kernel

public theorem checked : Checked 1605632 1613824 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1605632 128 c1605632) (checkChunk_sound 1605760 128 c1605760)) (Checked.append (checkChunk_sound 1605888 128 c1605888) (checkChunk_sound 1606016 128 c1606016))) (Checked.append (Checked.append (checkChunk_sound 1606144 128 c1606144) (checkChunk_sound 1606272 128 c1606272)) (Checked.append (checkChunk_sound 1606400 128 c1606400) (checkChunk_sound 1606528 128 c1606528)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1606656 128 c1606656) (checkChunk_sound 1606784 128 c1606784)) (Checked.append (checkChunk_sound 1606912 128 c1606912) (checkChunk_sound 1607040 128 c1607040))) (Checked.append (Checked.append (checkChunk_sound 1607168 128 c1607168) (checkChunk_sound 1607296 128 c1607296)) (Checked.append (checkChunk_sound 1607424 128 c1607424) (checkChunk_sound 1607552 128 c1607552))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1607680 128 c1607680) (checkChunk_sound 1607808 128 c1607808)) (Checked.append (checkChunk_sound 1607936 128 c1607936) (checkChunk_sound 1608064 128 c1608064))) (Checked.append (Checked.append (checkChunk_sound 1608192 128 c1608192) (checkChunk_sound 1608320 128 c1608320)) (Checked.append (checkChunk_sound 1608448 128 c1608448) (checkChunk_sound 1608576 128 c1608576)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1608704 128 c1608704) (checkChunk_sound 1608832 128 c1608832)) (Checked.append (checkChunk_sound 1608960 128 c1608960) (checkChunk_sound 1609088 128 c1609088))) (Checked.append (Checked.append (checkChunk_sound 1609216 128 c1609216) (checkChunk_sound 1609344 128 c1609344)) (Checked.append (checkChunk_sound 1609472 128 c1609472) (checkChunk_sound 1609600 128 c1609600)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1609728 128 c1609728) (checkChunk_sound 1609856 128 c1609856)) (Checked.append (checkChunk_sound 1609984 128 c1609984) (checkChunk_sound 1610112 128 c1610112))) (Checked.append (Checked.append (checkChunk_sound 1610240 128 c1610240) (checkChunk_sound 1610368 128 c1610368)) (Checked.append (checkChunk_sound 1610496 128 c1610496) (checkChunk_sound 1610624 128 c1610624)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1610752 128 c1610752) (checkChunk_sound 1610880 128 c1610880)) (Checked.append (checkChunk_sound 1611008 128 c1611008) (checkChunk_sound 1611136 128 c1611136))) (Checked.append (Checked.append (checkChunk_sound 1611264 128 c1611264) (checkChunk_sound 1611392 128 c1611392)) (Checked.append (checkChunk_sound 1611520 128 c1611520) (checkChunk_sound 1611648 128 c1611648))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1611776 128 c1611776) (checkChunk_sound 1611904 128 c1611904)) (Checked.append (checkChunk_sound 1612032 128 c1612032) (checkChunk_sound 1612160 128 c1612160))) (Checked.append (Checked.append (checkChunk_sound 1612288 128 c1612288) (checkChunk_sound 1612416 128 c1612416)) (Checked.append (checkChunk_sound 1612544 128 c1612544) (checkChunk_sound 1612672 128 c1612672)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1612800 128 c1612800) (checkChunk_sound 1612928 128 c1612928)) (Checked.append (checkChunk_sound 1613056 128 c1613056) (checkChunk_sound 1613184 128 c1613184))) (Checked.append (Checked.append (checkChunk_sound 1613312 128 c1613312) (checkChunk_sound 1613440 128 c1613440)) (Checked.append (checkChunk_sound 1613568 128 c1613568) (checkChunk_sound 1613696 128 c1613696)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B013
