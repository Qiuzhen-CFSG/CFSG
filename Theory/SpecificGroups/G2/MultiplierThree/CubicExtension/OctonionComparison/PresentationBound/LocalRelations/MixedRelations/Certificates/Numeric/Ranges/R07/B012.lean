module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1597440, 1605632).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B012
private theorem c1597440 : checkChunk 1597440 128 = true := by decide +kernel
private theorem c1597568 : checkChunk 1597568 128 = true := by decide +kernel
private theorem c1597696 : checkChunk 1597696 128 = true := by decide +kernel
private theorem c1597824 : checkChunk 1597824 128 = true := by decide +kernel
private theorem c1597952 : checkChunk 1597952 128 = true := by decide +kernel
private theorem c1598080 : checkChunk 1598080 128 = true := by decide +kernel
private theorem c1598208 : checkChunk 1598208 128 = true := by decide +kernel
private theorem c1598336 : checkChunk 1598336 128 = true := by decide +kernel
private theorem c1598464 : checkChunk 1598464 128 = true := by decide +kernel
private theorem c1598592 : checkChunk 1598592 128 = true := by decide +kernel
private theorem c1598720 : checkChunk 1598720 128 = true := by decide +kernel
private theorem c1598848 : checkChunk 1598848 128 = true := by decide +kernel
private theorem c1598976 : checkChunk 1598976 128 = true := by decide +kernel
private theorem c1599104 : checkChunk 1599104 128 = true := by decide +kernel
private theorem c1599232 : checkChunk 1599232 128 = true := by decide +kernel
private theorem c1599360 : checkChunk 1599360 128 = true := by decide +kernel
private theorem c1599488 : checkChunk 1599488 128 = true := by decide +kernel
private theorem c1599616 : checkChunk 1599616 128 = true := by decide +kernel
private theorem c1599744 : checkChunk 1599744 128 = true := by decide +kernel
private theorem c1599872 : checkChunk 1599872 128 = true := by decide +kernel
private theorem c1600000 : checkChunk 1600000 128 = true := by decide +kernel
private theorem c1600128 : checkChunk 1600128 128 = true := by decide +kernel
private theorem c1600256 : checkChunk 1600256 128 = true := by decide +kernel
private theorem c1600384 : checkChunk 1600384 128 = true := by decide +kernel
private theorem c1600512 : checkChunk 1600512 128 = true := by decide +kernel
private theorem c1600640 : checkChunk 1600640 128 = true := by decide +kernel
private theorem c1600768 : checkChunk 1600768 128 = true := by decide +kernel
private theorem c1600896 : checkChunk 1600896 128 = true := by decide +kernel
private theorem c1601024 : checkChunk 1601024 128 = true := by decide +kernel
private theorem c1601152 : checkChunk 1601152 128 = true := by decide +kernel
private theorem c1601280 : checkChunk 1601280 128 = true := by decide +kernel
private theorem c1601408 : checkChunk 1601408 128 = true := by decide +kernel
private theorem c1601536 : checkChunk 1601536 128 = true := by decide +kernel
private theorem c1601664 : checkChunk 1601664 128 = true := by decide +kernel
private theorem c1601792 : checkChunk 1601792 128 = true := by decide +kernel
private theorem c1601920 : checkChunk 1601920 128 = true := by decide +kernel
private theorem c1602048 : checkChunk 1602048 128 = true := by decide +kernel
private theorem c1602176 : checkChunk 1602176 128 = true := by decide +kernel
private theorem c1602304 : checkChunk 1602304 128 = true := by decide +kernel
private theorem c1602432 : checkChunk 1602432 128 = true := by decide +kernel
private theorem c1602560 : checkChunk 1602560 128 = true := by decide +kernel
private theorem c1602688 : checkChunk 1602688 128 = true := by decide +kernel
private theorem c1602816 : checkChunk 1602816 128 = true := by decide +kernel
private theorem c1602944 : checkChunk 1602944 128 = true := by decide +kernel
private theorem c1603072 : checkChunk 1603072 128 = true := by decide +kernel
private theorem c1603200 : checkChunk 1603200 128 = true := by decide +kernel
private theorem c1603328 : checkChunk 1603328 128 = true := by decide +kernel
private theorem c1603456 : checkChunk 1603456 128 = true := by decide +kernel
private theorem c1603584 : checkChunk 1603584 128 = true := by decide +kernel
private theorem c1603712 : checkChunk 1603712 128 = true := by decide +kernel
private theorem c1603840 : checkChunk 1603840 128 = true := by decide +kernel
private theorem c1603968 : checkChunk 1603968 128 = true := by decide +kernel
private theorem c1604096 : checkChunk 1604096 128 = true := by decide +kernel
private theorem c1604224 : checkChunk 1604224 128 = true := by decide +kernel
private theorem c1604352 : checkChunk 1604352 128 = true := by decide +kernel
private theorem c1604480 : checkChunk 1604480 128 = true := by decide +kernel
private theorem c1604608 : checkChunk 1604608 128 = true := by decide +kernel
private theorem c1604736 : checkChunk 1604736 128 = true := by decide +kernel
private theorem c1604864 : checkChunk 1604864 128 = true := by decide +kernel
private theorem c1604992 : checkChunk 1604992 128 = true := by decide +kernel
private theorem c1605120 : checkChunk 1605120 128 = true := by decide +kernel
private theorem c1605248 : checkChunk 1605248 128 = true := by decide +kernel
private theorem c1605376 : checkChunk 1605376 128 = true := by decide +kernel
private theorem c1605504 : checkChunk 1605504 128 = true := by decide +kernel

public theorem checked : Checked 1597440 1605632 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1597440 128 c1597440) (checkChunk_sound 1597568 128 c1597568)) (Checked.append (checkChunk_sound 1597696 128 c1597696) (checkChunk_sound 1597824 128 c1597824))) (Checked.append (Checked.append (checkChunk_sound 1597952 128 c1597952) (checkChunk_sound 1598080 128 c1598080)) (Checked.append (checkChunk_sound 1598208 128 c1598208) (checkChunk_sound 1598336 128 c1598336)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1598464 128 c1598464) (checkChunk_sound 1598592 128 c1598592)) (Checked.append (checkChunk_sound 1598720 128 c1598720) (checkChunk_sound 1598848 128 c1598848))) (Checked.append (Checked.append (checkChunk_sound 1598976 128 c1598976) (checkChunk_sound 1599104 128 c1599104)) (Checked.append (checkChunk_sound 1599232 128 c1599232) (checkChunk_sound 1599360 128 c1599360))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1599488 128 c1599488) (checkChunk_sound 1599616 128 c1599616)) (Checked.append (checkChunk_sound 1599744 128 c1599744) (checkChunk_sound 1599872 128 c1599872))) (Checked.append (Checked.append (checkChunk_sound 1600000 128 c1600000) (checkChunk_sound 1600128 128 c1600128)) (Checked.append (checkChunk_sound 1600256 128 c1600256) (checkChunk_sound 1600384 128 c1600384)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1600512 128 c1600512) (checkChunk_sound 1600640 128 c1600640)) (Checked.append (checkChunk_sound 1600768 128 c1600768) (checkChunk_sound 1600896 128 c1600896))) (Checked.append (Checked.append (checkChunk_sound 1601024 128 c1601024) (checkChunk_sound 1601152 128 c1601152)) (Checked.append (checkChunk_sound 1601280 128 c1601280) (checkChunk_sound 1601408 128 c1601408)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1601536 128 c1601536) (checkChunk_sound 1601664 128 c1601664)) (Checked.append (checkChunk_sound 1601792 128 c1601792) (checkChunk_sound 1601920 128 c1601920))) (Checked.append (Checked.append (checkChunk_sound 1602048 128 c1602048) (checkChunk_sound 1602176 128 c1602176)) (Checked.append (checkChunk_sound 1602304 128 c1602304) (checkChunk_sound 1602432 128 c1602432)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1602560 128 c1602560) (checkChunk_sound 1602688 128 c1602688)) (Checked.append (checkChunk_sound 1602816 128 c1602816) (checkChunk_sound 1602944 128 c1602944))) (Checked.append (Checked.append (checkChunk_sound 1603072 128 c1603072) (checkChunk_sound 1603200 128 c1603200)) (Checked.append (checkChunk_sound 1603328 128 c1603328) (checkChunk_sound 1603456 128 c1603456))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1603584 128 c1603584) (checkChunk_sound 1603712 128 c1603712)) (Checked.append (checkChunk_sound 1603840 128 c1603840) (checkChunk_sound 1603968 128 c1603968))) (Checked.append (Checked.append (checkChunk_sound 1604096 128 c1604096) (checkChunk_sound 1604224 128 c1604224)) (Checked.append (checkChunk_sound 1604352 128 c1604352) (checkChunk_sound 1604480 128 c1604480)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1604608 128 c1604608) (checkChunk_sound 1604736 128 c1604736)) (Checked.append (checkChunk_sound 1604864 128 c1604864) (checkChunk_sound 1604992 128 c1604992))) (Checked.append (Checked.append (checkChunk_sound 1605120 128 c1605120) (checkChunk_sound 1605248 128 c1605248)) (Checked.append (checkChunk_sound 1605376 128 c1605376) (checkChunk_sound 1605504 128 c1605504)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B012
