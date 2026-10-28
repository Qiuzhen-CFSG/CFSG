module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1474560, 1482752).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B023
private theorem c1474560 : checkChunk 1474560 128 = true := by decide +kernel
private theorem c1474688 : checkChunk 1474688 128 = true := by decide +kernel
private theorem c1474816 : checkChunk 1474816 128 = true := by decide +kernel
private theorem c1474944 : checkChunk 1474944 128 = true := by decide +kernel
private theorem c1475072 : checkChunk 1475072 128 = true := by decide +kernel
private theorem c1475200 : checkChunk 1475200 128 = true := by decide +kernel
private theorem c1475328 : checkChunk 1475328 128 = true := by decide +kernel
private theorem c1475456 : checkChunk 1475456 128 = true := by decide +kernel
private theorem c1475584 : checkChunk 1475584 128 = true := by decide +kernel
private theorem c1475712 : checkChunk 1475712 128 = true := by decide +kernel
private theorem c1475840 : checkChunk 1475840 128 = true := by decide +kernel
private theorem c1475968 : checkChunk 1475968 128 = true := by decide +kernel
private theorem c1476096 : checkChunk 1476096 128 = true := by decide +kernel
private theorem c1476224 : checkChunk 1476224 128 = true := by decide +kernel
private theorem c1476352 : checkChunk 1476352 128 = true := by decide +kernel
private theorem c1476480 : checkChunk 1476480 128 = true := by decide +kernel
private theorem c1476608 : checkChunk 1476608 128 = true := by decide +kernel
private theorem c1476736 : checkChunk 1476736 128 = true := by decide +kernel
private theorem c1476864 : checkChunk 1476864 128 = true := by decide +kernel
private theorem c1476992 : checkChunk 1476992 128 = true := by decide +kernel
private theorem c1477120 : checkChunk 1477120 128 = true := by decide +kernel
private theorem c1477248 : checkChunk 1477248 128 = true := by decide +kernel
private theorem c1477376 : checkChunk 1477376 128 = true := by decide +kernel
private theorem c1477504 : checkChunk 1477504 128 = true := by decide +kernel
private theorem c1477632 : checkChunk 1477632 128 = true := by decide +kernel
private theorem c1477760 : checkChunk 1477760 128 = true := by decide +kernel
private theorem c1477888 : checkChunk 1477888 128 = true := by decide +kernel
private theorem c1478016 : checkChunk 1478016 128 = true := by decide +kernel
private theorem c1478144 : checkChunk 1478144 128 = true := by decide +kernel
private theorem c1478272 : checkChunk 1478272 128 = true := by decide +kernel
private theorem c1478400 : checkChunk 1478400 128 = true := by decide +kernel
private theorem c1478528 : checkChunk 1478528 128 = true := by decide +kernel
private theorem c1478656 : checkChunk 1478656 128 = true := by decide +kernel
private theorem c1478784 : checkChunk 1478784 128 = true := by decide +kernel
private theorem c1478912 : checkChunk 1478912 128 = true := by decide +kernel
private theorem c1479040 : checkChunk 1479040 128 = true := by decide +kernel
private theorem c1479168 : checkChunk 1479168 128 = true := by decide +kernel
private theorem c1479296 : checkChunk 1479296 128 = true := by decide +kernel
private theorem c1479424 : checkChunk 1479424 128 = true := by decide +kernel
private theorem c1479552 : checkChunk 1479552 128 = true := by decide +kernel
private theorem c1479680 : checkChunk 1479680 128 = true := by decide +kernel
private theorem c1479808 : checkChunk 1479808 128 = true := by decide +kernel
private theorem c1479936 : checkChunk 1479936 128 = true := by decide +kernel
private theorem c1480064 : checkChunk 1480064 128 = true := by decide +kernel
private theorem c1480192 : checkChunk 1480192 128 = true := by decide +kernel
private theorem c1480320 : checkChunk 1480320 128 = true := by decide +kernel
private theorem c1480448 : checkChunk 1480448 128 = true := by decide +kernel
private theorem c1480576 : checkChunk 1480576 128 = true := by decide +kernel
private theorem c1480704 : checkChunk 1480704 128 = true := by decide +kernel
private theorem c1480832 : checkChunk 1480832 128 = true := by decide +kernel
private theorem c1480960 : checkChunk 1480960 128 = true := by decide +kernel
private theorem c1481088 : checkChunk 1481088 128 = true := by decide +kernel
private theorem c1481216 : checkChunk 1481216 128 = true := by decide +kernel
private theorem c1481344 : checkChunk 1481344 128 = true := by decide +kernel
private theorem c1481472 : checkChunk 1481472 128 = true := by decide +kernel
private theorem c1481600 : checkChunk 1481600 128 = true := by decide +kernel
private theorem c1481728 : checkChunk 1481728 128 = true := by decide +kernel
private theorem c1481856 : checkChunk 1481856 128 = true := by decide +kernel
private theorem c1481984 : checkChunk 1481984 128 = true := by decide +kernel
private theorem c1482112 : checkChunk 1482112 128 = true := by decide +kernel
private theorem c1482240 : checkChunk 1482240 128 = true := by decide +kernel
private theorem c1482368 : checkChunk 1482368 128 = true := by decide +kernel
private theorem c1482496 : checkChunk 1482496 128 = true := by decide +kernel
private theorem c1482624 : checkChunk 1482624 128 = true := by decide +kernel

public theorem checked : Checked 1474560 1482752 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1474560 128 c1474560) (checkChunk_sound 1474688 128 c1474688)) (Checked.append (checkChunk_sound 1474816 128 c1474816) (checkChunk_sound 1474944 128 c1474944))) (Checked.append (Checked.append (checkChunk_sound 1475072 128 c1475072) (checkChunk_sound 1475200 128 c1475200)) (Checked.append (checkChunk_sound 1475328 128 c1475328) (checkChunk_sound 1475456 128 c1475456)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1475584 128 c1475584) (checkChunk_sound 1475712 128 c1475712)) (Checked.append (checkChunk_sound 1475840 128 c1475840) (checkChunk_sound 1475968 128 c1475968))) (Checked.append (Checked.append (checkChunk_sound 1476096 128 c1476096) (checkChunk_sound 1476224 128 c1476224)) (Checked.append (checkChunk_sound 1476352 128 c1476352) (checkChunk_sound 1476480 128 c1476480))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1476608 128 c1476608) (checkChunk_sound 1476736 128 c1476736)) (Checked.append (checkChunk_sound 1476864 128 c1476864) (checkChunk_sound 1476992 128 c1476992))) (Checked.append (Checked.append (checkChunk_sound 1477120 128 c1477120) (checkChunk_sound 1477248 128 c1477248)) (Checked.append (checkChunk_sound 1477376 128 c1477376) (checkChunk_sound 1477504 128 c1477504)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1477632 128 c1477632) (checkChunk_sound 1477760 128 c1477760)) (Checked.append (checkChunk_sound 1477888 128 c1477888) (checkChunk_sound 1478016 128 c1478016))) (Checked.append (Checked.append (checkChunk_sound 1478144 128 c1478144) (checkChunk_sound 1478272 128 c1478272)) (Checked.append (checkChunk_sound 1478400 128 c1478400) (checkChunk_sound 1478528 128 c1478528)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1478656 128 c1478656) (checkChunk_sound 1478784 128 c1478784)) (Checked.append (checkChunk_sound 1478912 128 c1478912) (checkChunk_sound 1479040 128 c1479040))) (Checked.append (Checked.append (checkChunk_sound 1479168 128 c1479168) (checkChunk_sound 1479296 128 c1479296)) (Checked.append (checkChunk_sound 1479424 128 c1479424) (checkChunk_sound 1479552 128 c1479552)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1479680 128 c1479680) (checkChunk_sound 1479808 128 c1479808)) (Checked.append (checkChunk_sound 1479936 128 c1479936) (checkChunk_sound 1480064 128 c1480064))) (Checked.append (Checked.append (checkChunk_sound 1480192 128 c1480192) (checkChunk_sound 1480320 128 c1480320)) (Checked.append (checkChunk_sound 1480448 128 c1480448) (checkChunk_sound 1480576 128 c1480576))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1480704 128 c1480704) (checkChunk_sound 1480832 128 c1480832)) (Checked.append (checkChunk_sound 1480960 128 c1480960) (checkChunk_sound 1481088 128 c1481088))) (Checked.append (Checked.append (checkChunk_sound 1481216 128 c1481216) (checkChunk_sound 1481344 128 c1481344)) (Checked.append (checkChunk_sound 1481472 128 c1481472) (checkChunk_sound 1481600 128 c1481600)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1481728 128 c1481728) (checkChunk_sound 1481856 128 c1481856)) (Checked.append (checkChunk_sound 1481984 128 c1481984) (checkChunk_sound 1482112 128 c1482112))) (Checked.append (Checked.append (checkChunk_sound 1482240 128 c1482240) (checkChunk_sound 1482368 128 c1482368)) (Checked.append (checkChunk_sound 1482496 128 c1482496) (checkChunk_sound 1482624 128 c1482624)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B023
