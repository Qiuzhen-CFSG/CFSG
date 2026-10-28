module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [237568, 245760).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B002
private theorem c237568 : checkChunk 237568 128 = true := by decide +kernel
private theorem c237696 : checkChunk 237696 128 = true := by decide +kernel
private theorem c237824 : checkChunk 237824 128 = true := by decide +kernel
private theorem c237952 : checkChunk 237952 128 = true := by decide +kernel
private theorem c238080 : checkChunk 238080 128 = true := by decide +kernel
private theorem c238208 : checkChunk 238208 128 = true := by decide +kernel
private theorem c238336 : checkChunk 238336 128 = true := by decide +kernel
private theorem c238464 : checkChunk 238464 128 = true := by decide +kernel
private theorem c238592 : checkChunk 238592 128 = true := by decide +kernel
private theorem c238720 : checkChunk 238720 128 = true := by decide +kernel
private theorem c238848 : checkChunk 238848 128 = true := by decide +kernel
private theorem c238976 : checkChunk 238976 128 = true := by decide +kernel
private theorem c239104 : checkChunk 239104 128 = true := by decide +kernel
private theorem c239232 : checkChunk 239232 128 = true := by decide +kernel
private theorem c239360 : checkChunk 239360 128 = true := by decide +kernel
private theorem c239488 : checkChunk 239488 128 = true := by decide +kernel
private theorem c239616 : checkChunk 239616 128 = true := by decide +kernel
private theorem c239744 : checkChunk 239744 128 = true := by decide +kernel
private theorem c239872 : checkChunk 239872 128 = true := by decide +kernel
private theorem c240000 : checkChunk 240000 128 = true := by decide +kernel
private theorem c240128 : checkChunk 240128 128 = true := by decide +kernel
private theorem c240256 : checkChunk 240256 128 = true := by decide +kernel
private theorem c240384 : checkChunk 240384 128 = true := by decide +kernel
private theorem c240512 : checkChunk 240512 128 = true := by decide +kernel
private theorem c240640 : checkChunk 240640 128 = true := by decide +kernel
private theorem c240768 : checkChunk 240768 128 = true := by decide +kernel
private theorem c240896 : checkChunk 240896 128 = true := by decide +kernel
private theorem c241024 : checkChunk 241024 128 = true := by decide +kernel
private theorem c241152 : checkChunk 241152 128 = true := by decide +kernel
private theorem c241280 : checkChunk 241280 128 = true := by decide +kernel
private theorem c241408 : checkChunk 241408 128 = true := by decide +kernel
private theorem c241536 : checkChunk 241536 128 = true := by decide +kernel
private theorem c241664 : checkChunk 241664 128 = true := by decide +kernel
private theorem c241792 : checkChunk 241792 128 = true := by decide +kernel
private theorem c241920 : checkChunk 241920 128 = true := by decide +kernel
private theorem c242048 : checkChunk 242048 128 = true := by decide +kernel
private theorem c242176 : checkChunk 242176 128 = true := by decide +kernel
private theorem c242304 : checkChunk 242304 128 = true := by decide +kernel
private theorem c242432 : checkChunk 242432 128 = true := by decide +kernel
private theorem c242560 : checkChunk 242560 128 = true := by decide +kernel
private theorem c242688 : checkChunk 242688 128 = true := by decide +kernel
private theorem c242816 : checkChunk 242816 128 = true := by decide +kernel
private theorem c242944 : checkChunk 242944 128 = true := by decide +kernel
private theorem c243072 : checkChunk 243072 128 = true := by decide +kernel
private theorem c243200 : checkChunk 243200 128 = true := by decide +kernel
private theorem c243328 : checkChunk 243328 128 = true := by decide +kernel
private theorem c243456 : checkChunk 243456 128 = true := by decide +kernel
private theorem c243584 : checkChunk 243584 128 = true := by decide +kernel
private theorem c243712 : checkChunk 243712 128 = true := by decide +kernel
private theorem c243840 : checkChunk 243840 128 = true := by decide +kernel
private theorem c243968 : checkChunk 243968 128 = true := by decide +kernel
private theorem c244096 : checkChunk 244096 128 = true := by decide +kernel
private theorem c244224 : checkChunk 244224 128 = true := by decide +kernel
private theorem c244352 : checkChunk 244352 128 = true := by decide +kernel
private theorem c244480 : checkChunk 244480 128 = true := by decide +kernel
private theorem c244608 : checkChunk 244608 128 = true := by decide +kernel
private theorem c244736 : checkChunk 244736 128 = true := by decide +kernel
private theorem c244864 : checkChunk 244864 128 = true := by decide +kernel
private theorem c244992 : checkChunk 244992 128 = true := by decide +kernel
private theorem c245120 : checkChunk 245120 128 = true := by decide +kernel
private theorem c245248 : checkChunk 245248 128 = true := by decide +kernel
private theorem c245376 : checkChunk 245376 128 = true := by decide +kernel
private theorem c245504 : checkChunk 245504 128 = true := by decide +kernel
private theorem c245632 : checkChunk 245632 128 = true := by decide +kernel

public theorem checked : Checked 237568 245760 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 237568 128 c237568) (checkChunk_sound 237696 128 c237696)) (Checked.append (checkChunk_sound 237824 128 c237824) (checkChunk_sound 237952 128 c237952))) (Checked.append (Checked.append (checkChunk_sound 238080 128 c238080) (checkChunk_sound 238208 128 c238208)) (Checked.append (checkChunk_sound 238336 128 c238336) (checkChunk_sound 238464 128 c238464)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 238592 128 c238592) (checkChunk_sound 238720 128 c238720)) (Checked.append (checkChunk_sound 238848 128 c238848) (checkChunk_sound 238976 128 c238976))) (Checked.append (Checked.append (checkChunk_sound 239104 128 c239104) (checkChunk_sound 239232 128 c239232)) (Checked.append (checkChunk_sound 239360 128 c239360) (checkChunk_sound 239488 128 c239488))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 239616 128 c239616) (checkChunk_sound 239744 128 c239744)) (Checked.append (checkChunk_sound 239872 128 c239872) (checkChunk_sound 240000 128 c240000))) (Checked.append (Checked.append (checkChunk_sound 240128 128 c240128) (checkChunk_sound 240256 128 c240256)) (Checked.append (checkChunk_sound 240384 128 c240384) (checkChunk_sound 240512 128 c240512)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 240640 128 c240640) (checkChunk_sound 240768 128 c240768)) (Checked.append (checkChunk_sound 240896 128 c240896) (checkChunk_sound 241024 128 c241024))) (Checked.append (Checked.append (checkChunk_sound 241152 128 c241152) (checkChunk_sound 241280 128 c241280)) (Checked.append (checkChunk_sound 241408 128 c241408) (checkChunk_sound 241536 128 c241536)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 241664 128 c241664) (checkChunk_sound 241792 128 c241792)) (Checked.append (checkChunk_sound 241920 128 c241920) (checkChunk_sound 242048 128 c242048))) (Checked.append (Checked.append (checkChunk_sound 242176 128 c242176) (checkChunk_sound 242304 128 c242304)) (Checked.append (checkChunk_sound 242432 128 c242432) (checkChunk_sound 242560 128 c242560)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 242688 128 c242688) (checkChunk_sound 242816 128 c242816)) (Checked.append (checkChunk_sound 242944 128 c242944) (checkChunk_sound 243072 128 c243072))) (Checked.append (Checked.append (checkChunk_sound 243200 128 c243200) (checkChunk_sound 243328 128 c243328)) (Checked.append (checkChunk_sound 243456 128 c243456) (checkChunk_sound 243584 128 c243584))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 243712 128 c243712) (checkChunk_sound 243840 128 c243840)) (Checked.append (checkChunk_sound 243968 128 c243968) (checkChunk_sound 244096 128 c244096))) (Checked.append (Checked.append (checkChunk_sound 244224 128 c244224) (checkChunk_sound 244352 128 c244352)) (Checked.append (checkChunk_sound 244480 128 c244480) (checkChunk_sound 244608 128 c244608)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 244736 128 c244736) (checkChunk_sound 244864 128 c244864)) (Checked.append (checkChunk_sound 244992 128 c244992) (checkChunk_sound 245120 128 c245120))) (Checked.append (Checked.append (checkChunk_sound 245248 128 c245248) (checkChunk_sound 245376 128 c245376)) (Checked.append (checkChunk_sound 245504 128 c245504) (checkChunk_sound 245632 128 c245632)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B002
