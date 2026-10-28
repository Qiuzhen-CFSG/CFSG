module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [32768, 40960).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B003
private theorem c32768 : checkChunk 32768 128 = true := by decide +kernel
private theorem c32896 : checkChunk 32896 128 = true := by decide +kernel
private theorem c33024 : checkChunk 33024 128 = true := by decide +kernel
private theorem c33152 : checkChunk 33152 128 = true := by decide +kernel
private theorem c33280 : checkChunk 33280 128 = true := by decide +kernel
private theorem c33408 : checkChunk 33408 128 = true := by decide +kernel
private theorem c33536 : checkChunk 33536 128 = true := by decide +kernel
private theorem c33664 : checkChunk 33664 128 = true := by decide +kernel
private theorem c33792 : checkChunk 33792 128 = true := by decide +kernel
private theorem c33920 : checkChunk 33920 128 = true := by decide +kernel
private theorem c34048 : checkChunk 34048 128 = true := by decide +kernel
private theorem c34176 : checkChunk 34176 128 = true := by decide +kernel
private theorem c34304 : checkChunk 34304 128 = true := by decide +kernel
private theorem c34432 : checkChunk 34432 128 = true := by decide +kernel
private theorem c34560 : checkChunk 34560 128 = true := by decide +kernel
private theorem c34688 : checkChunk 34688 128 = true := by decide +kernel
private theorem c34816 : checkChunk 34816 128 = true := by decide +kernel
private theorem c34944 : checkChunk 34944 128 = true := by decide +kernel
private theorem c35072 : checkChunk 35072 128 = true := by decide +kernel
private theorem c35200 : checkChunk 35200 128 = true := by decide +kernel
private theorem c35328 : checkChunk 35328 128 = true := by decide +kernel
private theorem c35456 : checkChunk 35456 128 = true := by decide +kernel
private theorem c35584 : checkChunk 35584 128 = true := by decide +kernel
private theorem c35712 : checkChunk 35712 128 = true := by decide +kernel
private theorem c35840 : checkChunk 35840 128 = true := by decide +kernel
private theorem c35968 : checkChunk 35968 128 = true := by decide +kernel
private theorem c36096 : checkChunk 36096 128 = true := by decide +kernel
private theorem c36224 : checkChunk 36224 128 = true := by decide +kernel
private theorem c36352 : checkChunk 36352 128 = true := by decide +kernel
private theorem c36480 : checkChunk 36480 128 = true := by decide +kernel
private theorem c36608 : checkChunk 36608 128 = true := by decide +kernel
private theorem c36736 : checkChunk 36736 128 = true := by decide +kernel
private theorem c36864 : checkChunk 36864 128 = true := by decide +kernel
private theorem c36992 : checkChunk 36992 128 = true := by decide +kernel
private theorem c37120 : checkChunk 37120 128 = true := by decide +kernel
private theorem c37248 : checkChunk 37248 128 = true := by decide +kernel
private theorem c37376 : checkChunk 37376 128 = true := by decide +kernel
private theorem c37504 : checkChunk 37504 128 = true := by decide +kernel
private theorem c37632 : checkChunk 37632 128 = true := by decide +kernel
private theorem c37760 : checkChunk 37760 128 = true := by decide +kernel
private theorem c37888 : checkChunk 37888 128 = true := by decide +kernel
private theorem c38016 : checkChunk 38016 128 = true := by decide +kernel
private theorem c38144 : checkChunk 38144 128 = true := by decide +kernel
private theorem c38272 : checkChunk 38272 128 = true := by decide +kernel
private theorem c38400 : checkChunk 38400 128 = true := by decide +kernel
private theorem c38528 : checkChunk 38528 128 = true := by decide +kernel
private theorem c38656 : checkChunk 38656 128 = true := by decide +kernel
private theorem c38784 : checkChunk 38784 128 = true := by decide +kernel
private theorem c38912 : checkChunk 38912 128 = true := by decide +kernel
private theorem c39040 : checkChunk 39040 128 = true := by decide +kernel
private theorem c39168 : checkChunk 39168 128 = true := by decide +kernel
private theorem c39296 : checkChunk 39296 128 = true := by decide +kernel
private theorem c39424 : checkChunk 39424 128 = true := by decide +kernel
private theorem c39552 : checkChunk 39552 128 = true := by decide +kernel
private theorem c39680 : checkChunk 39680 128 = true := by decide +kernel
private theorem c39808 : checkChunk 39808 128 = true := by decide +kernel
private theorem c39936 : checkChunk 39936 128 = true := by decide +kernel
private theorem c40064 : checkChunk 40064 128 = true := by decide +kernel
private theorem c40192 : checkChunk 40192 128 = true := by decide +kernel
private theorem c40320 : checkChunk 40320 128 = true := by decide +kernel
private theorem c40448 : checkChunk 40448 128 = true := by decide +kernel
private theorem c40576 : checkChunk 40576 128 = true := by decide +kernel
private theorem c40704 : checkChunk 40704 128 = true := by decide +kernel
private theorem c40832 : checkChunk 40832 128 = true := by decide +kernel

public theorem checked : Checked 32768 40960 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 32768 128 c32768) (checkChunk_sound 32896 128 c32896)) (Checked.append (checkChunk_sound 33024 128 c33024) (checkChunk_sound 33152 128 c33152))) (Checked.append (Checked.append (checkChunk_sound 33280 128 c33280) (checkChunk_sound 33408 128 c33408)) (Checked.append (checkChunk_sound 33536 128 c33536) (checkChunk_sound 33664 128 c33664)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 33792 128 c33792) (checkChunk_sound 33920 128 c33920)) (Checked.append (checkChunk_sound 34048 128 c34048) (checkChunk_sound 34176 128 c34176))) (Checked.append (Checked.append (checkChunk_sound 34304 128 c34304) (checkChunk_sound 34432 128 c34432)) (Checked.append (checkChunk_sound 34560 128 c34560) (checkChunk_sound 34688 128 c34688))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 34816 128 c34816) (checkChunk_sound 34944 128 c34944)) (Checked.append (checkChunk_sound 35072 128 c35072) (checkChunk_sound 35200 128 c35200))) (Checked.append (Checked.append (checkChunk_sound 35328 128 c35328) (checkChunk_sound 35456 128 c35456)) (Checked.append (checkChunk_sound 35584 128 c35584) (checkChunk_sound 35712 128 c35712)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 35840 128 c35840) (checkChunk_sound 35968 128 c35968)) (Checked.append (checkChunk_sound 36096 128 c36096) (checkChunk_sound 36224 128 c36224))) (Checked.append (Checked.append (checkChunk_sound 36352 128 c36352) (checkChunk_sound 36480 128 c36480)) (Checked.append (checkChunk_sound 36608 128 c36608) (checkChunk_sound 36736 128 c36736)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 36864 128 c36864) (checkChunk_sound 36992 128 c36992)) (Checked.append (checkChunk_sound 37120 128 c37120) (checkChunk_sound 37248 128 c37248))) (Checked.append (Checked.append (checkChunk_sound 37376 128 c37376) (checkChunk_sound 37504 128 c37504)) (Checked.append (checkChunk_sound 37632 128 c37632) (checkChunk_sound 37760 128 c37760)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 37888 128 c37888) (checkChunk_sound 38016 128 c38016)) (Checked.append (checkChunk_sound 38144 128 c38144) (checkChunk_sound 38272 128 c38272))) (Checked.append (Checked.append (checkChunk_sound 38400 128 c38400) (checkChunk_sound 38528 128 c38528)) (Checked.append (checkChunk_sound 38656 128 c38656) (checkChunk_sound 38784 128 c38784))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 38912 128 c38912) (checkChunk_sound 39040 128 c39040)) (Checked.append (checkChunk_sound 39168 128 c39168) (checkChunk_sound 39296 128 c39296))) (Checked.append (Checked.append (checkChunk_sound 39424 128 c39424) (checkChunk_sound 39552 128 c39552)) (Checked.append (checkChunk_sound 39680 128 c39680) (checkChunk_sound 39808 128 c39808)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 39936 128 c39936) (checkChunk_sound 40064 128 c40064)) (Checked.append (checkChunk_sound 40192 128 c40192) (checkChunk_sound 40320 128 c40320))) (Checked.append (Checked.append (checkChunk_sound 40448 128 c40448) (checkChunk_sound 40576 128 c40576)) (Checked.append (checkChunk_sound 40704 128 c40704) (checkChunk_sound 40832 128 c40832)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B003
