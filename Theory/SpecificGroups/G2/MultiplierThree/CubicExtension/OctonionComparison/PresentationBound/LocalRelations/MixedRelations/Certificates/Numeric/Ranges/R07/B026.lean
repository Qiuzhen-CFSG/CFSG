module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1712128, 1718562).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B026
private theorem c1712128 : checkChunk 1712128 128 = true := by decide +kernel
private theorem c1712256 : checkChunk 1712256 128 = true := by decide +kernel
private theorem c1712384 : checkChunk 1712384 128 = true := by decide +kernel
private theorem c1712512 : checkChunk 1712512 128 = true := by decide +kernel
private theorem c1712640 : checkChunk 1712640 128 = true := by decide +kernel
private theorem c1712768 : checkChunk 1712768 128 = true := by decide +kernel
private theorem c1712896 : checkChunk 1712896 128 = true := by decide +kernel
private theorem c1713024 : checkChunk 1713024 128 = true := by decide +kernel
private theorem c1713152 : checkChunk 1713152 128 = true := by decide +kernel
private theorem c1713280 : checkChunk 1713280 128 = true := by decide +kernel
private theorem c1713408 : checkChunk 1713408 128 = true := by decide +kernel
private theorem c1713536 : checkChunk 1713536 128 = true := by decide +kernel
private theorem c1713664 : checkChunk 1713664 128 = true := by decide +kernel
private theorem c1713792 : checkChunk 1713792 128 = true := by decide +kernel
private theorem c1713920 : checkChunk 1713920 128 = true := by decide +kernel
private theorem c1714048 : checkChunk 1714048 128 = true := by decide +kernel
private theorem c1714176 : checkChunk 1714176 128 = true := by decide +kernel
private theorem c1714304 : checkChunk 1714304 128 = true := by decide +kernel
private theorem c1714432 : checkChunk 1714432 128 = true := by decide +kernel
private theorem c1714560 : checkChunk 1714560 128 = true := by decide +kernel
private theorem c1714688 : checkChunk 1714688 128 = true := by decide +kernel
private theorem c1714816 : checkChunk 1714816 128 = true := by decide +kernel
private theorem c1714944 : checkChunk 1714944 128 = true := by decide +kernel
private theorem c1715072 : checkChunk 1715072 128 = true := by decide +kernel
private theorem c1715200 : checkChunk 1715200 128 = true := by decide +kernel
private theorem c1715328 : checkChunk 1715328 128 = true := by decide +kernel
private theorem c1715456 : checkChunk 1715456 128 = true := by decide +kernel
private theorem c1715584 : checkChunk 1715584 128 = true := by decide +kernel
private theorem c1715712 : checkChunk 1715712 128 = true := by decide +kernel
private theorem c1715840 : checkChunk 1715840 128 = true := by decide +kernel
private theorem c1715968 : checkChunk 1715968 128 = true := by decide +kernel
private theorem c1716096 : checkChunk 1716096 128 = true := by decide +kernel
private theorem c1716224 : checkChunk 1716224 128 = true := by decide +kernel
private theorem c1716352 : checkChunk 1716352 128 = true := by decide +kernel
private theorem c1716480 : checkChunk 1716480 128 = true := by decide +kernel
private theorem c1716608 : checkChunk 1716608 128 = true := by decide +kernel
private theorem c1716736 : checkChunk 1716736 128 = true := by decide +kernel
private theorem c1716864 : checkChunk 1716864 128 = true := by decide +kernel
private theorem c1716992 : checkChunk 1716992 128 = true := by decide +kernel
private theorem c1717120 : checkChunk 1717120 128 = true := by decide +kernel
private theorem c1717248 : checkChunk 1717248 128 = true := by decide +kernel
private theorem c1717376 : checkChunk 1717376 128 = true := by decide +kernel
private theorem c1717504 : checkChunk 1717504 128 = true := by decide +kernel
private theorem c1717632 : checkChunk 1717632 128 = true := by decide +kernel
private theorem c1717760 : checkChunk 1717760 128 = true := by decide +kernel
private theorem c1717888 : checkChunk 1717888 128 = true := by decide +kernel
private theorem c1718016 : checkChunk 1718016 128 = true := by decide +kernel
private theorem c1718144 : checkChunk 1718144 128 = true := by decide +kernel
private theorem c1718272 : checkChunk 1718272 128 = true := by decide +kernel
private theorem c1718400 : checkChunk 1718400 128 = true := by decide +kernel
private theorem c1718528 : checkChunk 1718528 34 = true := by decide +kernel

public theorem checked : Checked 1712128 1718562 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1712128 128 c1712128) (Checked.append (checkChunk_sound 1712256 128 c1712256) (checkChunk_sound 1712384 128 c1712384))) (Checked.append (checkChunk_sound 1712512 128 c1712512) (Checked.append (checkChunk_sound 1712640 128 c1712640) (checkChunk_sound 1712768 128 c1712768)))) (Checked.append (Checked.append (checkChunk_sound 1712896 128 c1712896) (Checked.append (checkChunk_sound 1713024 128 c1713024) (checkChunk_sound 1713152 128 c1713152))) (Checked.append (checkChunk_sound 1713280 128 c1713280) (Checked.append (checkChunk_sound 1713408 128 c1713408) (checkChunk_sound 1713536 128 c1713536))))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1713664 128 c1713664) (Checked.append (checkChunk_sound 1713792 128 c1713792) (checkChunk_sound 1713920 128 c1713920))) (Checked.append (checkChunk_sound 1714048 128 c1714048) (Checked.append (checkChunk_sound 1714176 128 c1714176) (checkChunk_sound 1714304 128 c1714304)))) (Checked.append (Checked.append (checkChunk_sound 1714432 128 c1714432) (Checked.append (checkChunk_sound 1714560 128 c1714560) (checkChunk_sound 1714688 128 c1714688))) (Checked.append (Checked.append (checkChunk_sound 1714816 128 c1714816) (checkChunk_sound 1714944 128 c1714944)) (Checked.append (checkChunk_sound 1715072 128 c1715072) (checkChunk_sound 1715200 128 c1715200)))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1715328 128 c1715328) (Checked.append (checkChunk_sound 1715456 128 c1715456) (checkChunk_sound 1715584 128 c1715584))) (Checked.append (checkChunk_sound 1715712 128 c1715712) (Checked.append (checkChunk_sound 1715840 128 c1715840) (checkChunk_sound 1715968 128 c1715968)))) (Checked.append (Checked.append (checkChunk_sound 1716096 128 c1716096) (Checked.append (checkChunk_sound 1716224 128 c1716224) (checkChunk_sound 1716352 128 c1716352))) (Checked.append (Checked.append (checkChunk_sound 1716480 128 c1716480) (checkChunk_sound 1716608 128 c1716608)) (Checked.append (checkChunk_sound 1716736 128 c1716736) (checkChunk_sound 1716864 128 c1716864))))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1716992 128 c1716992) (Checked.append (checkChunk_sound 1717120 128 c1717120) (checkChunk_sound 1717248 128 c1717248))) (Checked.append (checkChunk_sound 1717376 128 c1717376) (Checked.append (checkChunk_sound 1717504 128 c1717504) (checkChunk_sound 1717632 128 c1717632)))) (Checked.append (Checked.append (checkChunk_sound 1717760 128 c1717760) (Checked.append (checkChunk_sound 1717888 128 c1717888) (checkChunk_sound 1718016 128 c1718016))) (Checked.append (Checked.append (checkChunk_sound 1718144 128 c1718144) (checkChunk_sound 1718272 128 c1718272)) (Checked.append (checkChunk_sound 1718400 128 c1718400) (checkChunk_sound 1718528 34 c1718528)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B026
