module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1671168, 1679360).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B021
private theorem c1671168 : checkChunk 1671168 128 = true := by decide +kernel
private theorem c1671296 : checkChunk 1671296 128 = true := by decide +kernel
private theorem c1671424 : checkChunk 1671424 128 = true := by decide +kernel
private theorem c1671552 : checkChunk 1671552 128 = true := by decide +kernel
private theorem c1671680 : checkChunk 1671680 128 = true := by decide +kernel
private theorem c1671808 : checkChunk 1671808 128 = true := by decide +kernel
private theorem c1671936 : checkChunk 1671936 128 = true := by decide +kernel
private theorem c1672064 : checkChunk 1672064 128 = true := by decide +kernel
private theorem c1672192 : checkChunk 1672192 128 = true := by decide +kernel
private theorem c1672320 : checkChunk 1672320 128 = true := by decide +kernel
private theorem c1672448 : checkChunk 1672448 128 = true := by decide +kernel
private theorem c1672576 : checkChunk 1672576 128 = true := by decide +kernel
private theorem c1672704 : checkChunk 1672704 128 = true := by decide +kernel
private theorem c1672832 : checkChunk 1672832 128 = true := by decide +kernel
private theorem c1672960 : checkChunk 1672960 128 = true := by decide +kernel
private theorem c1673088 : checkChunk 1673088 128 = true := by decide +kernel
private theorem c1673216 : checkChunk 1673216 128 = true := by decide +kernel
private theorem c1673344 : checkChunk 1673344 128 = true := by decide +kernel
private theorem c1673472 : checkChunk 1673472 128 = true := by decide +kernel
private theorem c1673600 : checkChunk 1673600 128 = true := by decide +kernel
private theorem c1673728 : checkChunk 1673728 128 = true := by decide +kernel
private theorem c1673856 : checkChunk 1673856 128 = true := by decide +kernel
private theorem c1673984 : checkChunk 1673984 128 = true := by decide +kernel
private theorem c1674112 : checkChunk 1674112 128 = true := by decide +kernel
private theorem c1674240 : checkChunk 1674240 128 = true := by decide +kernel
private theorem c1674368 : checkChunk 1674368 128 = true := by decide +kernel
private theorem c1674496 : checkChunk 1674496 128 = true := by decide +kernel
private theorem c1674624 : checkChunk 1674624 128 = true := by decide +kernel
private theorem c1674752 : checkChunk 1674752 128 = true := by decide +kernel
private theorem c1674880 : checkChunk 1674880 128 = true := by decide +kernel
private theorem c1675008 : checkChunk 1675008 128 = true := by decide +kernel
private theorem c1675136 : checkChunk 1675136 128 = true := by decide +kernel
private theorem c1675264 : checkChunk 1675264 128 = true := by decide +kernel
private theorem c1675392 : checkChunk 1675392 128 = true := by decide +kernel
private theorem c1675520 : checkChunk 1675520 128 = true := by decide +kernel
private theorem c1675648 : checkChunk 1675648 128 = true := by decide +kernel
private theorem c1675776 : checkChunk 1675776 128 = true := by decide +kernel
private theorem c1675904 : checkChunk 1675904 128 = true := by decide +kernel
private theorem c1676032 : checkChunk 1676032 128 = true := by decide +kernel
private theorem c1676160 : checkChunk 1676160 128 = true := by decide +kernel
private theorem c1676288 : checkChunk 1676288 128 = true := by decide +kernel
private theorem c1676416 : checkChunk 1676416 128 = true := by decide +kernel
private theorem c1676544 : checkChunk 1676544 128 = true := by decide +kernel
private theorem c1676672 : checkChunk 1676672 128 = true := by decide +kernel
private theorem c1676800 : checkChunk 1676800 128 = true := by decide +kernel
private theorem c1676928 : checkChunk 1676928 128 = true := by decide +kernel
private theorem c1677056 : checkChunk 1677056 128 = true := by decide +kernel
private theorem c1677184 : checkChunk 1677184 128 = true := by decide +kernel
private theorem c1677312 : checkChunk 1677312 128 = true := by decide +kernel
private theorem c1677440 : checkChunk 1677440 128 = true := by decide +kernel
private theorem c1677568 : checkChunk 1677568 128 = true := by decide +kernel
private theorem c1677696 : checkChunk 1677696 128 = true := by decide +kernel
private theorem c1677824 : checkChunk 1677824 128 = true := by decide +kernel
private theorem c1677952 : checkChunk 1677952 128 = true := by decide +kernel
private theorem c1678080 : checkChunk 1678080 128 = true := by decide +kernel
private theorem c1678208 : checkChunk 1678208 128 = true := by decide +kernel
private theorem c1678336 : checkChunk 1678336 128 = true := by decide +kernel
private theorem c1678464 : checkChunk 1678464 128 = true := by decide +kernel
private theorem c1678592 : checkChunk 1678592 128 = true := by decide +kernel
private theorem c1678720 : checkChunk 1678720 128 = true := by decide +kernel
private theorem c1678848 : checkChunk 1678848 128 = true := by decide +kernel
private theorem c1678976 : checkChunk 1678976 128 = true := by decide +kernel
private theorem c1679104 : checkChunk 1679104 128 = true := by decide +kernel
private theorem c1679232 : checkChunk 1679232 128 = true := by decide +kernel

public theorem checked : Checked 1671168 1679360 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1671168 128 c1671168) (checkChunk_sound 1671296 128 c1671296)) (Checked.append (checkChunk_sound 1671424 128 c1671424) (checkChunk_sound 1671552 128 c1671552))) (Checked.append (Checked.append (checkChunk_sound 1671680 128 c1671680) (checkChunk_sound 1671808 128 c1671808)) (Checked.append (checkChunk_sound 1671936 128 c1671936) (checkChunk_sound 1672064 128 c1672064)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1672192 128 c1672192) (checkChunk_sound 1672320 128 c1672320)) (Checked.append (checkChunk_sound 1672448 128 c1672448) (checkChunk_sound 1672576 128 c1672576))) (Checked.append (Checked.append (checkChunk_sound 1672704 128 c1672704) (checkChunk_sound 1672832 128 c1672832)) (Checked.append (checkChunk_sound 1672960 128 c1672960) (checkChunk_sound 1673088 128 c1673088))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1673216 128 c1673216) (checkChunk_sound 1673344 128 c1673344)) (Checked.append (checkChunk_sound 1673472 128 c1673472) (checkChunk_sound 1673600 128 c1673600))) (Checked.append (Checked.append (checkChunk_sound 1673728 128 c1673728) (checkChunk_sound 1673856 128 c1673856)) (Checked.append (checkChunk_sound 1673984 128 c1673984) (checkChunk_sound 1674112 128 c1674112)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1674240 128 c1674240) (checkChunk_sound 1674368 128 c1674368)) (Checked.append (checkChunk_sound 1674496 128 c1674496) (checkChunk_sound 1674624 128 c1674624))) (Checked.append (Checked.append (checkChunk_sound 1674752 128 c1674752) (checkChunk_sound 1674880 128 c1674880)) (Checked.append (checkChunk_sound 1675008 128 c1675008) (checkChunk_sound 1675136 128 c1675136)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1675264 128 c1675264) (checkChunk_sound 1675392 128 c1675392)) (Checked.append (checkChunk_sound 1675520 128 c1675520) (checkChunk_sound 1675648 128 c1675648))) (Checked.append (Checked.append (checkChunk_sound 1675776 128 c1675776) (checkChunk_sound 1675904 128 c1675904)) (Checked.append (checkChunk_sound 1676032 128 c1676032) (checkChunk_sound 1676160 128 c1676160)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1676288 128 c1676288) (checkChunk_sound 1676416 128 c1676416)) (Checked.append (checkChunk_sound 1676544 128 c1676544) (checkChunk_sound 1676672 128 c1676672))) (Checked.append (Checked.append (checkChunk_sound 1676800 128 c1676800) (checkChunk_sound 1676928 128 c1676928)) (Checked.append (checkChunk_sound 1677056 128 c1677056) (checkChunk_sound 1677184 128 c1677184))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1677312 128 c1677312) (checkChunk_sound 1677440 128 c1677440)) (Checked.append (checkChunk_sound 1677568 128 c1677568) (checkChunk_sound 1677696 128 c1677696))) (Checked.append (Checked.append (checkChunk_sound 1677824 128 c1677824) (checkChunk_sound 1677952 128 c1677952)) (Checked.append (checkChunk_sound 1678080 128 c1678080) (checkChunk_sound 1678208 128 c1678208)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1678336 128 c1678336) (checkChunk_sound 1678464 128 c1678464)) (Checked.append (checkChunk_sound 1678592 128 c1678592) (checkChunk_sound 1678720 128 c1678720))) (Checked.append (Checked.append (checkChunk_sound 1678848 128 c1678848) (checkChunk_sound 1678976 128 c1678976)) (Checked.append (checkChunk_sound 1679104 128 c1679104) (checkChunk_sound 1679232 128 c1679232)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B021
