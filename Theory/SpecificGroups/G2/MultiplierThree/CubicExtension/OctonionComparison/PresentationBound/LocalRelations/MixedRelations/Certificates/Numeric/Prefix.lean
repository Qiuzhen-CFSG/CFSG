module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! First 8192 instructions of the pinned ATLAS cyclic trace.
Every local calculation is checked by the kernel, then passed to Pooled.check. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric
private theorem c0 : checkChunk 0 128 = true := by decide +kernel
private theorem c128 : checkChunk 128 128 = true := by decide +kernel
private theorem c256 : checkChunk 256 128 = true := by decide +kernel
private theorem c384 : checkChunk 384 128 = true := by decide +kernel
private theorem c512 : checkChunk 512 128 = true := by decide +kernel
private theorem c640 : checkChunk 640 128 = true := by decide +kernel
private theorem c768 : checkChunk 768 128 = true := by decide +kernel
private theorem c896 : checkChunk 896 128 = true := by decide +kernel
private theorem c1024 : checkChunk 1024 128 = true := by decide +kernel
private theorem c1152 : checkChunk 1152 128 = true := by decide +kernel
private theorem c1280 : checkChunk 1280 128 = true := by decide +kernel
private theorem c1408 : checkChunk 1408 128 = true := by decide +kernel
private theorem c1536 : checkChunk 1536 128 = true := by decide +kernel
private theorem c1664 : checkChunk 1664 128 = true := by decide +kernel
private theorem c1792 : checkChunk 1792 128 = true := by decide +kernel
private theorem c1920 : checkChunk 1920 128 = true := by decide +kernel
private theorem c2048 : checkChunk 2048 128 = true := by decide +kernel
private theorem c2176 : checkChunk 2176 128 = true := by decide +kernel
private theorem c2304 : checkChunk 2304 128 = true := by decide +kernel
private theorem c2432 : checkChunk 2432 128 = true := by decide +kernel
private theorem c2560 : checkChunk 2560 128 = true := by decide +kernel
private theorem c2688 : checkChunk 2688 128 = true := by decide +kernel
private theorem c2816 : checkChunk 2816 128 = true := by decide +kernel
private theorem c2944 : checkChunk 2944 128 = true := by decide +kernel
private theorem c3072 : checkChunk 3072 128 = true := by decide +kernel
private theorem c3200 : checkChunk 3200 128 = true := by decide +kernel
private theorem c3328 : checkChunk 3328 128 = true := by decide +kernel
private theorem c3456 : checkChunk 3456 128 = true := by decide +kernel
private theorem c3584 : checkChunk 3584 128 = true := by decide +kernel
private theorem c3712 : checkChunk 3712 128 = true := by decide +kernel
private theorem c3840 : checkChunk 3840 128 = true := by decide +kernel
private theorem c3968 : checkChunk 3968 128 = true := by decide +kernel
private theorem c4096 : checkChunk 4096 128 = true := by decide +kernel
private theorem c4224 : checkChunk 4224 128 = true := by decide +kernel
private theorem c4352 : checkChunk 4352 128 = true := by decide +kernel
private theorem c4480 : checkChunk 4480 128 = true := by decide +kernel
private theorem c4608 : checkChunk 4608 128 = true := by decide +kernel
private theorem c4736 : checkChunk 4736 128 = true := by decide +kernel
private theorem c4864 : checkChunk 4864 128 = true := by decide +kernel
private theorem c4992 : checkChunk 4992 128 = true := by decide +kernel
private theorem c5120 : checkChunk 5120 128 = true := by decide +kernel
private theorem c5248 : checkChunk 5248 128 = true := by decide +kernel
private theorem c5376 : checkChunk 5376 128 = true := by decide +kernel
private theorem c5504 : checkChunk 5504 128 = true := by decide +kernel
private theorem c5632 : checkChunk 5632 128 = true := by decide +kernel
private theorem c5760 : checkChunk 5760 128 = true := by decide +kernel
private theorem c5888 : checkChunk 5888 128 = true := by decide +kernel
private theorem c6016 : checkChunk 6016 128 = true := by decide +kernel
private theorem c6144 : checkChunk 6144 128 = true := by decide +kernel
private theorem c6272 : checkChunk 6272 128 = true := by decide +kernel
private theorem c6400 : checkChunk 6400 128 = true := by decide +kernel
private theorem c6528 : checkChunk 6528 128 = true := by decide +kernel
private theorem c6656 : checkChunk 6656 128 = true := by decide +kernel
private theorem c6784 : checkChunk 6784 128 = true := by decide +kernel
private theorem c6912 : checkChunk 6912 128 = true := by decide +kernel
private theorem c7040 : checkChunk 7040 128 = true := by decide +kernel
private theorem c7168 : checkChunk 7168 128 = true := by decide +kernel
private theorem c7296 : checkChunk 7296 128 = true := by decide +kernel
private theorem c7424 : checkChunk 7424 128 = true := by decide +kernel
private theorem c7552 : checkChunk 7552 128 = true := by decide +kernel
private theorem c7680 : checkChunk 7680 128 = true := by decide +kernel
private theorem c7808 : checkChunk 7808 128 = true := by decide +kernel
private theorem c7936 : checkChunk 7936 128 = true := by decide +kernel
private theorem c8064 : checkChunk 8064 128 = true := by decide +kernel

public theorem checkedPrefix : Checked 0 8192 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 0 128 c0) (checkChunk_sound 128 128 c128)) (Checked.append (checkChunk_sound 256 128 c256) (checkChunk_sound 384 128 c384))) (Checked.append (Checked.append (checkChunk_sound 512 128 c512) (checkChunk_sound 640 128 c640)) (Checked.append (checkChunk_sound 768 128 c768) (checkChunk_sound 896 128 c896)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1024 128 c1024) (checkChunk_sound 1152 128 c1152)) (Checked.append (checkChunk_sound 1280 128 c1280) (checkChunk_sound 1408 128 c1408))) (Checked.append (Checked.append (checkChunk_sound 1536 128 c1536) (checkChunk_sound 1664 128 c1664)) (Checked.append (checkChunk_sound 1792 128 c1792) (checkChunk_sound 1920 128 c1920))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 2048 128 c2048) (checkChunk_sound 2176 128 c2176)) (Checked.append (checkChunk_sound 2304 128 c2304) (checkChunk_sound 2432 128 c2432))) (Checked.append (Checked.append (checkChunk_sound 2560 128 c2560) (checkChunk_sound 2688 128 c2688)) (Checked.append (checkChunk_sound 2816 128 c2816) (checkChunk_sound 2944 128 c2944)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 3072 128 c3072) (checkChunk_sound 3200 128 c3200)) (Checked.append (checkChunk_sound 3328 128 c3328) (checkChunk_sound 3456 128 c3456))) (Checked.append (Checked.append (checkChunk_sound 3584 128 c3584) (checkChunk_sound 3712 128 c3712)) (Checked.append (checkChunk_sound 3840 128 c3840) (checkChunk_sound 3968 128 c3968)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 4096 128 c4096) (checkChunk_sound 4224 128 c4224)) (Checked.append (checkChunk_sound 4352 128 c4352) (checkChunk_sound 4480 128 c4480))) (Checked.append (Checked.append (checkChunk_sound 4608 128 c4608) (checkChunk_sound 4736 128 c4736)) (Checked.append (checkChunk_sound 4864 128 c4864) (checkChunk_sound 4992 128 c4992)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 5120 128 c5120) (checkChunk_sound 5248 128 c5248)) (Checked.append (checkChunk_sound 5376 128 c5376) (checkChunk_sound 5504 128 c5504))) (Checked.append (Checked.append (checkChunk_sound 5632 128 c5632) (checkChunk_sound 5760 128 c5760)) (Checked.append (checkChunk_sound 5888 128 c5888) (checkChunk_sound 6016 128 c6016))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 6144 128 c6144) (checkChunk_sound 6272 128 c6272)) (Checked.append (checkChunk_sound 6400 128 c6400) (checkChunk_sound 6528 128 c6528))) (Checked.append (Checked.append (checkChunk_sound 6656 128 c6656) (checkChunk_sound 6784 128 c6784)) (Checked.append (checkChunk_sound 6912 128 c6912) (checkChunk_sound 7040 128 c7040)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 7168 128 c7168) (checkChunk_sound 7296 128 c7296)) (Checked.append (checkChunk_sound 7424 128 c7424) (checkChunk_sound 7552 128 c7552))) (Checked.append (Checked.append (checkChunk_sound 7680 128 c7680) (checkChunk_sound 7808 128 c7808)) (Checked.append (checkChunk_sound 7936 128 c7936) (checkChunk_sound 8064 128 c8064)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric
