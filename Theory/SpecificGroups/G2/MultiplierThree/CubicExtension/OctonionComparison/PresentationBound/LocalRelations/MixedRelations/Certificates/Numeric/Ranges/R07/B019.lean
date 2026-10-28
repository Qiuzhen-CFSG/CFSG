module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1654784, 1662976).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B019
private theorem c1654784 : checkChunk 1654784 128 = true := by decide +kernel
private theorem c1654912 : checkChunk 1654912 128 = true := by decide +kernel
private theorem c1655040 : checkChunk 1655040 128 = true := by decide +kernel
private theorem c1655168 : checkChunk 1655168 128 = true := by decide +kernel
private theorem c1655296 : checkChunk 1655296 128 = true := by decide +kernel
private theorem c1655424 : checkChunk 1655424 128 = true := by decide +kernel
private theorem c1655552 : checkChunk 1655552 128 = true := by decide +kernel
private theorem c1655680 : checkChunk 1655680 128 = true := by decide +kernel
private theorem c1655808 : checkChunk 1655808 128 = true := by decide +kernel
private theorem c1655936 : checkChunk 1655936 128 = true := by decide +kernel
private theorem c1656064 : checkChunk 1656064 128 = true := by decide +kernel
private theorem c1656192 : checkChunk 1656192 128 = true := by decide +kernel
private theorem c1656320 : checkChunk 1656320 128 = true := by decide +kernel
private theorem c1656448 : checkChunk 1656448 128 = true := by decide +kernel
private theorem c1656576 : checkChunk 1656576 128 = true := by decide +kernel
private theorem c1656704 : checkChunk 1656704 128 = true := by decide +kernel
private theorem c1656832 : checkChunk 1656832 128 = true := by decide +kernel
private theorem c1656960 : checkChunk 1656960 128 = true := by decide +kernel
private theorem c1657088 : checkChunk 1657088 128 = true := by decide +kernel
private theorem c1657216 : checkChunk 1657216 128 = true := by decide +kernel
private theorem c1657344 : checkChunk 1657344 128 = true := by decide +kernel
private theorem c1657472 : checkChunk 1657472 128 = true := by decide +kernel
private theorem c1657600 : checkChunk 1657600 128 = true := by decide +kernel
private theorem c1657728 : checkChunk 1657728 128 = true := by decide +kernel
private theorem c1657856 : checkChunk 1657856 128 = true := by decide +kernel
private theorem c1657984 : checkChunk 1657984 128 = true := by decide +kernel
private theorem c1658112 : checkChunk 1658112 128 = true := by decide +kernel
private theorem c1658240 : checkChunk 1658240 128 = true := by decide +kernel
private theorem c1658368 : checkChunk 1658368 128 = true := by decide +kernel
private theorem c1658496 : checkChunk 1658496 128 = true := by decide +kernel
private theorem c1658624 : checkChunk 1658624 128 = true := by decide +kernel
private theorem c1658752 : checkChunk 1658752 128 = true := by decide +kernel
private theorem c1658880 : checkChunk 1658880 128 = true := by decide +kernel
private theorem c1659008 : checkChunk 1659008 128 = true := by decide +kernel
private theorem c1659136 : checkChunk 1659136 128 = true := by decide +kernel
private theorem c1659264 : checkChunk 1659264 128 = true := by decide +kernel
private theorem c1659392 : checkChunk 1659392 128 = true := by decide +kernel
private theorem c1659520 : checkChunk 1659520 128 = true := by decide +kernel
private theorem c1659648 : checkChunk 1659648 128 = true := by decide +kernel
private theorem c1659776 : checkChunk 1659776 128 = true := by decide +kernel
private theorem c1659904 : checkChunk 1659904 128 = true := by decide +kernel
private theorem c1660032 : checkChunk 1660032 128 = true := by decide +kernel
private theorem c1660160 : checkChunk 1660160 128 = true := by decide +kernel
private theorem c1660288 : checkChunk 1660288 128 = true := by decide +kernel
private theorem c1660416 : checkChunk 1660416 128 = true := by decide +kernel
private theorem c1660544 : checkChunk 1660544 128 = true := by decide +kernel
private theorem c1660672 : checkChunk 1660672 128 = true := by decide +kernel
private theorem c1660800 : checkChunk 1660800 128 = true := by decide +kernel
private theorem c1660928 : checkChunk 1660928 128 = true := by decide +kernel
private theorem c1661056 : checkChunk 1661056 128 = true := by decide +kernel
private theorem c1661184 : checkChunk 1661184 128 = true := by decide +kernel
private theorem c1661312 : checkChunk 1661312 128 = true := by decide +kernel
private theorem c1661440 : checkChunk 1661440 128 = true := by decide +kernel
private theorem c1661568 : checkChunk 1661568 128 = true := by decide +kernel
private theorem c1661696 : checkChunk 1661696 128 = true := by decide +kernel
private theorem c1661824 : checkChunk 1661824 128 = true := by decide +kernel
private theorem c1661952 : checkChunk 1661952 128 = true := by decide +kernel
private theorem c1662080 : checkChunk 1662080 128 = true := by decide +kernel
private theorem c1662208 : checkChunk 1662208 128 = true := by decide +kernel
private theorem c1662336 : checkChunk 1662336 128 = true := by decide +kernel
private theorem c1662464 : checkChunk 1662464 128 = true := by decide +kernel
private theorem c1662592 : checkChunk 1662592 128 = true := by decide +kernel
private theorem c1662720 : checkChunk 1662720 128 = true := by decide +kernel
private theorem c1662848 : checkChunk 1662848 128 = true := by decide +kernel

public theorem checked : Checked 1654784 1662976 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1654784 128 c1654784) (checkChunk_sound 1654912 128 c1654912)) (Checked.append (checkChunk_sound 1655040 128 c1655040) (checkChunk_sound 1655168 128 c1655168))) (Checked.append (Checked.append (checkChunk_sound 1655296 128 c1655296) (checkChunk_sound 1655424 128 c1655424)) (Checked.append (checkChunk_sound 1655552 128 c1655552) (checkChunk_sound 1655680 128 c1655680)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1655808 128 c1655808) (checkChunk_sound 1655936 128 c1655936)) (Checked.append (checkChunk_sound 1656064 128 c1656064) (checkChunk_sound 1656192 128 c1656192))) (Checked.append (Checked.append (checkChunk_sound 1656320 128 c1656320) (checkChunk_sound 1656448 128 c1656448)) (Checked.append (checkChunk_sound 1656576 128 c1656576) (checkChunk_sound 1656704 128 c1656704))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1656832 128 c1656832) (checkChunk_sound 1656960 128 c1656960)) (Checked.append (checkChunk_sound 1657088 128 c1657088) (checkChunk_sound 1657216 128 c1657216))) (Checked.append (Checked.append (checkChunk_sound 1657344 128 c1657344) (checkChunk_sound 1657472 128 c1657472)) (Checked.append (checkChunk_sound 1657600 128 c1657600) (checkChunk_sound 1657728 128 c1657728)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1657856 128 c1657856) (checkChunk_sound 1657984 128 c1657984)) (Checked.append (checkChunk_sound 1658112 128 c1658112) (checkChunk_sound 1658240 128 c1658240))) (Checked.append (Checked.append (checkChunk_sound 1658368 128 c1658368) (checkChunk_sound 1658496 128 c1658496)) (Checked.append (checkChunk_sound 1658624 128 c1658624) (checkChunk_sound 1658752 128 c1658752)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1658880 128 c1658880) (checkChunk_sound 1659008 128 c1659008)) (Checked.append (checkChunk_sound 1659136 128 c1659136) (checkChunk_sound 1659264 128 c1659264))) (Checked.append (Checked.append (checkChunk_sound 1659392 128 c1659392) (checkChunk_sound 1659520 128 c1659520)) (Checked.append (checkChunk_sound 1659648 128 c1659648) (checkChunk_sound 1659776 128 c1659776)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1659904 128 c1659904) (checkChunk_sound 1660032 128 c1660032)) (Checked.append (checkChunk_sound 1660160 128 c1660160) (checkChunk_sound 1660288 128 c1660288))) (Checked.append (Checked.append (checkChunk_sound 1660416 128 c1660416) (checkChunk_sound 1660544 128 c1660544)) (Checked.append (checkChunk_sound 1660672 128 c1660672) (checkChunk_sound 1660800 128 c1660800))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1660928 128 c1660928) (checkChunk_sound 1661056 128 c1661056)) (Checked.append (checkChunk_sound 1661184 128 c1661184) (checkChunk_sound 1661312 128 c1661312))) (Checked.append (Checked.append (checkChunk_sound 1661440 128 c1661440) (checkChunk_sound 1661568 128 c1661568)) (Checked.append (checkChunk_sound 1661696 128 c1661696) (checkChunk_sound 1661824 128 c1661824)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1661952 128 c1661952) (checkChunk_sound 1662080 128 c1662080)) (Checked.append (checkChunk_sound 1662208 128 c1662208) (checkChunk_sound 1662336 128 c1662336))) (Checked.append (Checked.append (checkChunk_sound 1662464 128 c1662464) (checkChunk_sound 1662592 128 c1662592)) (Checked.append (checkChunk_sound 1662720 128 c1662720) (checkChunk_sound 1662848 128 c1662848)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B019
