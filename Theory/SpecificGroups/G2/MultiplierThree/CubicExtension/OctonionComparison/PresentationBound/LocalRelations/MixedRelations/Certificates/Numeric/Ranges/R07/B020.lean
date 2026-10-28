module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1662976, 1671168).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B020
private theorem c1662976 : checkChunk 1662976 128 = true := by decide +kernel
private theorem c1663104 : checkChunk 1663104 128 = true := by decide +kernel
private theorem c1663232 : checkChunk 1663232 128 = true := by decide +kernel
private theorem c1663360 : checkChunk 1663360 128 = true := by decide +kernel
private theorem c1663488 : checkChunk 1663488 128 = true := by decide +kernel
private theorem c1663616 : checkChunk 1663616 128 = true := by decide +kernel
private theorem c1663744 : checkChunk 1663744 128 = true := by decide +kernel
private theorem c1663872 : checkChunk 1663872 128 = true := by decide +kernel
private theorem c1664000 : checkChunk 1664000 128 = true := by decide +kernel
private theorem c1664128 : checkChunk 1664128 128 = true := by decide +kernel
private theorem c1664256 : checkChunk 1664256 128 = true := by decide +kernel
private theorem c1664384 : checkChunk 1664384 128 = true := by decide +kernel
private theorem c1664512 : checkChunk 1664512 128 = true := by decide +kernel
private theorem c1664640 : checkChunk 1664640 128 = true := by decide +kernel
private theorem c1664768 : checkChunk 1664768 128 = true := by decide +kernel
private theorem c1664896 : checkChunk 1664896 128 = true := by decide +kernel
private theorem c1665024 : checkChunk 1665024 128 = true := by decide +kernel
private theorem c1665152 : checkChunk 1665152 128 = true := by decide +kernel
private theorem c1665280 : checkChunk 1665280 128 = true := by decide +kernel
private theorem c1665408 : checkChunk 1665408 128 = true := by decide +kernel
private theorem c1665536 : checkChunk 1665536 128 = true := by decide +kernel
private theorem c1665664 : checkChunk 1665664 128 = true := by decide +kernel
private theorem c1665792 : checkChunk 1665792 128 = true := by decide +kernel
private theorem c1665920 : checkChunk 1665920 128 = true := by decide +kernel
private theorem c1666048 : checkChunk 1666048 128 = true := by decide +kernel
private theorem c1666176 : checkChunk 1666176 128 = true := by decide +kernel
private theorem c1666304 : checkChunk 1666304 128 = true := by decide +kernel
private theorem c1666432 : checkChunk 1666432 128 = true := by decide +kernel
private theorem c1666560 : checkChunk 1666560 128 = true := by decide +kernel
private theorem c1666688 : checkChunk 1666688 128 = true := by decide +kernel
private theorem c1666816 : checkChunk 1666816 128 = true := by decide +kernel
private theorem c1666944 : checkChunk 1666944 128 = true := by decide +kernel
private theorem c1667072 : checkChunk 1667072 128 = true := by decide +kernel
private theorem c1667200 : checkChunk 1667200 128 = true := by decide +kernel
private theorem c1667328 : checkChunk 1667328 128 = true := by decide +kernel
private theorem c1667456 : checkChunk 1667456 128 = true := by decide +kernel
private theorem c1667584 : checkChunk 1667584 128 = true := by decide +kernel
private theorem c1667712 : checkChunk 1667712 128 = true := by decide +kernel
private theorem c1667840 : checkChunk 1667840 128 = true := by decide +kernel
private theorem c1667968 : checkChunk 1667968 128 = true := by decide +kernel
private theorem c1668096 : checkChunk 1668096 128 = true := by decide +kernel
private theorem c1668224 : checkChunk 1668224 128 = true := by decide +kernel
private theorem c1668352 : checkChunk 1668352 128 = true := by decide +kernel
private theorem c1668480 : checkChunk 1668480 128 = true := by decide +kernel
private theorem c1668608 : checkChunk 1668608 128 = true := by decide +kernel
private theorem c1668736 : checkChunk 1668736 128 = true := by decide +kernel
private theorem c1668864 : checkChunk 1668864 128 = true := by decide +kernel
private theorem c1668992 : checkChunk 1668992 128 = true := by decide +kernel
private theorem c1669120 : checkChunk 1669120 128 = true := by decide +kernel
private theorem c1669248 : checkChunk 1669248 128 = true := by decide +kernel
private theorem c1669376 : checkChunk 1669376 128 = true := by decide +kernel
private theorem c1669504 : checkChunk 1669504 128 = true := by decide +kernel
private theorem c1669632 : checkChunk 1669632 128 = true := by decide +kernel
private theorem c1669760 : checkChunk 1669760 128 = true := by decide +kernel
private theorem c1669888 : checkChunk 1669888 128 = true := by decide +kernel
private theorem c1670016 : checkChunk 1670016 128 = true := by decide +kernel
private theorem c1670144 : checkChunk 1670144 128 = true := by decide +kernel
private theorem c1670272 : checkChunk 1670272 128 = true := by decide +kernel
private theorem c1670400 : checkChunk 1670400 128 = true := by decide +kernel
private theorem c1670528 : checkChunk 1670528 128 = true := by decide +kernel
private theorem c1670656 : checkChunk 1670656 128 = true := by decide +kernel
private theorem c1670784 : checkChunk 1670784 128 = true := by decide +kernel
private theorem c1670912 : checkChunk 1670912 128 = true := by decide +kernel
private theorem c1671040 : checkChunk 1671040 128 = true := by decide +kernel

public theorem checked : Checked 1662976 1671168 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1662976 128 c1662976) (checkChunk_sound 1663104 128 c1663104)) (Checked.append (checkChunk_sound 1663232 128 c1663232) (checkChunk_sound 1663360 128 c1663360))) (Checked.append (Checked.append (checkChunk_sound 1663488 128 c1663488) (checkChunk_sound 1663616 128 c1663616)) (Checked.append (checkChunk_sound 1663744 128 c1663744) (checkChunk_sound 1663872 128 c1663872)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1664000 128 c1664000) (checkChunk_sound 1664128 128 c1664128)) (Checked.append (checkChunk_sound 1664256 128 c1664256) (checkChunk_sound 1664384 128 c1664384))) (Checked.append (Checked.append (checkChunk_sound 1664512 128 c1664512) (checkChunk_sound 1664640 128 c1664640)) (Checked.append (checkChunk_sound 1664768 128 c1664768) (checkChunk_sound 1664896 128 c1664896))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1665024 128 c1665024) (checkChunk_sound 1665152 128 c1665152)) (Checked.append (checkChunk_sound 1665280 128 c1665280) (checkChunk_sound 1665408 128 c1665408))) (Checked.append (Checked.append (checkChunk_sound 1665536 128 c1665536) (checkChunk_sound 1665664 128 c1665664)) (Checked.append (checkChunk_sound 1665792 128 c1665792) (checkChunk_sound 1665920 128 c1665920)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1666048 128 c1666048) (checkChunk_sound 1666176 128 c1666176)) (Checked.append (checkChunk_sound 1666304 128 c1666304) (checkChunk_sound 1666432 128 c1666432))) (Checked.append (Checked.append (checkChunk_sound 1666560 128 c1666560) (checkChunk_sound 1666688 128 c1666688)) (Checked.append (checkChunk_sound 1666816 128 c1666816) (checkChunk_sound 1666944 128 c1666944)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1667072 128 c1667072) (checkChunk_sound 1667200 128 c1667200)) (Checked.append (checkChunk_sound 1667328 128 c1667328) (checkChunk_sound 1667456 128 c1667456))) (Checked.append (Checked.append (checkChunk_sound 1667584 128 c1667584) (checkChunk_sound 1667712 128 c1667712)) (Checked.append (checkChunk_sound 1667840 128 c1667840) (checkChunk_sound 1667968 128 c1667968)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1668096 128 c1668096) (checkChunk_sound 1668224 128 c1668224)) (Checked.append (checkChunk_sound 1668352 128 c1668352) (checkChunk_sound 1668480 128 c1668480))) (Checked.append (Checked.append (checkChunk_sound 1668608 128 c1668608) (checkChunk_sound 1668736 128 c1668736)) (Checked.append (checkChunk_sound 1668864 128 c1668864) (checkChunk_sound 1668992 128 c1668992))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1669120 128 c1669120) (checkChunk_sound 1669248 128 c1669248)) (Checked.append (checkChunk_sound 1669376 128 c1669376) (checkChunk_sound 1669504 128 c1669504))) (Checked.append (Checked.append (checkChunk_sound 1669632 128 c1669632) (checkChunk_sound 1669760 128 c1669760)) (Checked.append (checkChunk_sound 1669888 128 c1669888) (checkChunk_sound 1670016 128 c1670016)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1670144 128 c1670144) (checkChunk_sound 1670272 128 c1670272)) (Checked.append (checkChunk_sound 1670400 128 c1670400) (checkChunk_sound 1670528 128 c1670528))) (Checked.append (Checked.append (checkChunk_sound 1670656 128 c1670656) (checkChunk_sound 1670784 128 c1670784)) (Checked.append (checkChunk_sound 1670912 128 c1670912) (checkChunk_sound 1671040 128 c1671040)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B020
