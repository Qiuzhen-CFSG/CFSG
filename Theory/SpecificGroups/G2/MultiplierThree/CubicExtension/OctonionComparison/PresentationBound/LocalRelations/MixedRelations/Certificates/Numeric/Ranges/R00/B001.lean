module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [16384, 24576).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B001
private theorem c16384 : checkChunk 16384 128 = true := by decide +kernel
private theorem c16512 : checkChunk 16512 128 = true := by decide +kernel
private theorem c16640 : checkChunk 16640 128 = true := by decide +kernel
private theorem c16768 : checkChunk 16768 128 = true := by decide +kernel
private theorem c16896 : checkChunk 16896 128 = true := by decide +kernel
private theorem c17024 : checkChunk 17024 128 = true := by decide +kernel
private theorem c17152 : checkChunk 17152 128 = true := by decide +kernel
private theorem c17280 : checkChunk 17280 128 = true := by decide +kernel
private theorem c17408 : checkChunk 17408 128 = true := by decide +kernel
private theorem c17536 : checkChunk 17536 128 = true := by decide +kernel
private theorem c17664 : checkChunk 17664 128 = true := by decide +kernel
private theorem c17792 : checkChunk 17792 128 = true := by decide +kernel
private theorem c17920 : checkChunk 17920 128 = true := by decide +kernel
private theorem c18048 : checkChunk 18048 128 = true := by decide +kernel
private theorem c18176 : checkChunk 18176 128 = true := by decide +kernel
private theorem c18304 : checkChunk 18304 128 = true := by decide +kernel
private theorem c18432 : checkChunk 18432 128 = true := by decide +kernel
private theorem c18560 : checkChunk 18560 128 = true := by decide +kernel
private theorem c18688 : checkChunk 18688 128 = true := by decide +kernel
private theorem c18816 : checkChunk 18816 128 = true := by decide +kernel
private theorem c18944 : checkChunk 18944 128 = true := by decide +kernel
private theorem c19072 : checkChunk 19072 128 = true := by decide +kernel
private theorem c19200 : checkChunk 19200 128 = true := by decide +kernel
private theorem c19328 : checkChunk 19328 128 = true := by decide +kernel
private theorem c19456 : checkChunk 19456 128 = true := by decide +kernel
private theorem c19584 : checkChunk 19584 128 = true := by decide +kernel
private theorem c19712 : checkChunk 19712 128 = true := by decide +kernel
private theorem c19840 : checkChunk 19840 128 = true := by decide +kernel
private theorem c19968 : checkChunk 19968 128 = true := by decide +kernel
private theorem c20096 : checkChunk 20096 128 = true := by decide +kernel
private theorem c20224 : checkChunk 20224 128 = true := by decide +kernel
private theorem c20352 : checkChunk 20352 128 = true := by decide +kernel
private theorem c20480 : checkChunk 20480 128 = true := by decide +kernel
private theorem c20608 : checkChunk 20608 128 = true := by decide +kernel
private theorem c20736 : checkChunk 20736 128 = true := by decide +kernel
private theorem c20864 : checkChunk 20864 128 = true := by decide +kernel
private theorem c20992 : checkChunk 20992 128 = true := by decide +kernel
private theorem c21120 : checkChunk 21120 128 = true := by decide +kernel
private theorem c21248 : checkChunk 21248 128 = true := by decide +kernel
private theorem c21376 : checkChunk 21376 128 = true := by decide +kernel
private theorem c21504 : checkChunk 21504 128 = true := by decide +kernel
private theorem c21632 : checkChunk 21632 128 = true := by decide +kernel
private theorem c21760 : checkChunk 21760 128 = true := by decide +kernel
private theorem c21888 : checkChunk 21888 128 = true := by decide +kernel
private theorem c22016 : checkChunk 22016 128 = true := by decide +kernel
private theorem c22144 : checkChunk 22144 128 = true := by decide +kernel
private theorem c22272 : checkChunk 22272 128 = true := by decide +kernel
private theorem c22400 : checkChunk 22400 128 = true := by decide +kernel
private theorem c22528 : checkChunk 22528 128 = true := by decide +kernel
private theorem c22656 : checkChunk 22656 128 = true := by decide +kernel
private theorem c22784 : checkChunk 22784 128 = true := by decide +kernel
private theorem c22912 : checkChunk 22912 128 = true := by decide +kernel
private theorem c23040 : checkChunk 23040 128 = true := by decide +kernel
private theorem c23168 : checkChunk 23168 128 = true := by decide +kernel
private theorem c23296 : checkChunk 23296 128 = true := by decide +kernel
private theorem c23424 : checkChunk 23424 128 = true := by decide +kernel
private theorem c23552 : checkChunk 23552 128 = true := by decide +kernel
private theorem c23680 : checkChunk 23680 128 = true := by decide +kernel
private theorem c23808 : checkChunk 23808 128 = true := by decide +kernel
private theorem c23936 : checkChunk 23936 128 = true := by decide +kernel
private theorem c24064 : checkChunk 24064 128 = true := by decide +kernel
private theorem c24192 : checkChunk 24192 128 = true := by decide +kernel
private theorem c24320 : checkChunk 24320 128 = true := by decide +kernel
private theorem c24448 : checkChunk 24448 128 = true := by decide +kernel

public theorem checked : Checked 16384 24576 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 16384 128 c16384) (checkChunk_sound 16512 128 c16512)) (Checked.append (checkChunk_sound 16640 128 c16640) (checkChunk_sound 16768 128 c16768))) (Checked.append (Checked.append (checkChunk_sound 16896 128 c16896) (checkChunk_sound 17024 128 c17024)) (Checked.append (checkChunk_sound 17152 128 c17152) (checkChunk_sound 17280 128 c17280)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 17408 128 c17408) (checkChunk_sound 17536 128 c17536)) (Checked.append (checkChunk_sound 17664 128 c17664) (checkChunk_sound 17792 128 c17792))) (Checked.append (Checked.append (checkChunk_sound 17920 128 c17920) (checkChunk_sound 18048 128 c18048)) (Checked.append (checkChunk_sound 18176 128 c18176) (checkChunk_sound 18304 128 c18304))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 18432 128 c18432) (checkChunk_sound 18560 128 c18560)) (Checked.append (checkChunk_sound 18688 128 c18688) (checkChunk_sound 18816 128 c18816))) (Checked.append (Checked.append (checkChunk_sound 18944 128 c18944) (checkChunk_sound 19072 128 c19072)) (Checked.append (checkChunk_sound 19200 128 c19200) (checkChunk_sound 19328 128 c19328)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 19456 128 c19456) (checkChunk_sound 19584 128 c19584)) (Checked.append (checkChunk_sound 19712 128 c19712) (checkChunk_sound 19840 128 c19840))) (Checked.append (Checked.append (checkChunk_sound 19968 128 c19968) (checkChunk_sound 20096 128 c20096)) (Checked.append (checkChunk_sound 20224 128 c20224) (checkChunk_sound 20352 128 c20352)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 20480 128 c20480) (checkChunk_sound 20608 128 c20608)) (Checked.append (checkChunk_sound 20736 128 c20736) (checkChunk_sound 20864 128 c20864))) (Checked.append (Checked.append (checkChunk_sound 20992 128 c20992) (checkChunk_sound 21120 128 c21120)) (Checked.append (checkChunk_sound 21248 128 c21248) (checkChunk_sound 21376 128 c21376)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 21504 128 c21504) (checkChunk_sound 21632 128 c21632)) (Checked.append (checkChunk_sound 21760 128 c21760) (checkChunk_sound 21888 128 c21888))) (Checked.append (Checked.append (checkChunk_sound 22016 128 c22016) (checkChunk_sound 22144 128 c22144)) (Checked.append (checkChunk_sound 22272 128 c22272) (checkChunk_sound 22400 128 c22400))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 22528 128 c22528) (checkChunk_sound 22656 128 c22656)) (Checked.append (checkChunk_sound 22784 128 c22784) (checkChunk_sound 22912 128 c22912))) (Checked.append (Checked.append (checkChunk_sound 23040 128 c23040) (checkChunk_sound 23168 128 c23168)) (Checked.append (checkChunk_sound 23296 128 c23296) (checkChunk_sound 23424 128 c23424)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 23552 128 c23552) (checkChunk_sound 23680 128 c23680)) (Checked.append (checkChunk_sound 23808 128 c23808) (checkChunk_sound 23936 128 c23936))) (Checked.append (Checked.append (checkChunk_sound 24064 128 c24064) (checkChunk_sound 24192 128 c24192)) (Checked.append (checkChunk_sound 24320 128 c24320) (checkChunk_sound 24448 128 c24448)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B001
