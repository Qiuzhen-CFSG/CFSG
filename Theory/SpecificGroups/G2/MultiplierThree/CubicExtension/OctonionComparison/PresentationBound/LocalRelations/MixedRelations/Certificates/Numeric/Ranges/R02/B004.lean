module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [466944, 475136).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B004
private theorem c466944 : checkChunk 466944 128 = true := by decide +kernel
private theorem c467072 : checkChunk 467072 128 = true := by decide +kernel
private theorem c467200 : checkChunk 467200 128 = true := by decide +kernel
private theorem c467328 : checkChunk 467328 128 = true := by decide +kernel
private theorem c467456 : checkChunk 467456 128 = true := by decide +kernel
private theorem c467584 : checkChunk 467584 128 = true := by decide +kernel
private theorem c467712 : checkChunk 467712 128 = true := by decide +kernel
private theorem c467840 : checkChunk 467840 128 = true := by decide +kernel
private theorem c467968 : checkChunk 467968 128 = true := by decide +kernel
private theorem c468096 : checkChunk 468096 128 = true := by decide +kernel
private theorem c468224 : checkChunk 468224 128 = true := by decide +kernel
private theorem c468352 : checkChunk 468352 128 = true := by decide +kernel
private theorem c468480 : checkChunk 468480 128 = true := by decide +kernel
private theorem c468608 : checkChunk 468608 128 = true := by decide +kernel
private theorem c468736 : checkChunk 468736 128 = true := by decide +kernel
private theorem c468864 : checkChunk 468864 128 = true := by decide +kernel
private theorem c468992 : checkChunk 468992 128 = true := by decide +kernel
private theorem c469120 : checkChunk 469120 128 = true := by decide +kernel
private theorem c469248 : checkChunk 469248 128 = true := by decide +kernel
private theorem c469376 : checkChunk 469376 128 = true := by decide +kernel
private theorem c469504 : checkChunk 469504 128 = true := by decide +kernel
private theorem c469632 : checkChunk 469632 128 = true := by decide +kernel
private theorem c469760 : checkChunk 469760 128 = true := by decide +kernel
private theorem c469888 : checkChunk 469888 128 = true := by decide +kernel
private theorem c470016 : checkChunk 470016 128 = true := by decide +kernel
private theorem c470144 : checkChunk 470144 128 = true := by decide +kernel
private theorem c470272 : checkChunk 470272 128 = true := by decide +kernel
private theorem c470400 : checkChunk 470400 128 = true := by decide +kernel
private theorem c470528 : checkChunk 470528 128 = true := by decide +kernel
private theorem c470656 : checkChunk 470656 128 = true := by decide +kernel
private theorem c470784 : checkChunk 470784 128 = true := by decide +kernel
private theorem c470912 : checkChunk 470912 128 = true := by decide +kernel
private theorem c471040 : checkChunk 471040 128 = true := by decide +kernel
private theorem c471168 : checkChunk 471168 128 = true := by decide +kernel
private theorem c471296 : checkChunk 471296 128 = true := by decide +kernel
private theorem c471424 : checkChunk 471424 128 = true := by decide +kernel
private theorem c471552 : checkChunk 471552 128 = true := by decide +kernel
private theorem c471680 : checkChunk 471680 128 = true := by decide +kernel
private theorem c471808 : checkChunk 471808 128 = true := by decide +kernel
private theorem c471936 : checkChunk 471936 128 = true := by decide +kernel
private theorem c472064 : checkChunk 472064 128 = true := by decide +kernel
private theorem c472192 : checkChunk 472192 128 = true := by decide +kernel
private theorem c472320 : checkChunk 472320 128 = true := by decide +kernel
private theorem c472448 : checkChunk 472448 128 = true := by decide +kernel
private theorem c472576 : checkChunk 472576 128 = true := by decide +kernel
private theorem c472704 : checkChunk 472704 128 = true := by decide +kernel
private theorem c472832 : checkChunk 472832 128 = true := by decide +kernel
private theorem c472960 : checkChunk 472960 128 = true := by decide +kernel
private theorem c473088 : checkChunk 473088 128 = true := by decide +kernel
private theorem c473216 : checkChunk 473216 128 = true := by decide +kernel
private theorem c473344 : checkChunk 473344 128 = true := by decide +kernel
private theorem c473472 : checkChunk 473472 128 = true := by decide +kernel
private theorem c473600 : checkChunk 473600 128 = true := by decide +kernel
private theorem c473728 : checkChunk 473728 128 = true := by decide +kernel
private theorem c473856 : checkChunk 473856 128 = true := by decide +kernel
private theorem c473984 : checkChunk 473984 128 = true := by decide +kernel
private theorem c474112 : checkChunk 474112 128 = true := by decide +kernel
private theorem c474240 : checkChunk 474240 128 = true := by decide +kernel
private theorem c474368 : checkChunk 474368 128 = true := by decide +kernel
private theorem c474496 : checkChunk 474496 128 = true := by decide +kernel
private theorem c474624 : checkChunk 474624 128 = true := by decide +kernel
private theorem c474752 : checkChunk 474752 128 = true := by decide +kernel
private theorem c474880 : checkChunk 474880 128 = true := by decide +kernel
private theorem c475008 : checkChunk 475008 128 = true := by decide +kernel

public theorem checked : Checked 466944 475136 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 466944 128 c466944) (checkChunk_sound 467072 128 c467072)) (Checked.append (checkChunk_sound 467200 128 c467200) (checkChunk_sound 467328 128 c467328))) (Checked.append (Checked.append (checkChunk_sound 467456 128 c467456) (checkChunk_sound 467584 128 c467584)) (Checked.append (checkChunk_sound 467712 128 c467712) (checkChunk_sound 467840 128 c467840)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 467968 128 c467968) (checkChunk_sound 468096 128 c468096)) (Checked.append (checkChunk_sound 468224 128 c468224) (checkChunk_sound 468352 128 c468352))) (Checked.append (Checked.append (checkChunk_sound 468480 128 c468480) (checkChunk_sound 468608 128 c468608)) (Checked.append (checkChunk_sound 468736 128 c468736) (checkChunk_sound 468864 128 c468864))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 468992 128 c468992) (checkChunk_sound 469120 128 c469120)) (Checked.append (checkChunk_sound 469248 128 c469248) (checkChunk_sound 469376 128 c469376))) (Checked.append (Checked.append (checkChunk_sound 469504 128 c469504) (checkChunk_sound 469632 128 c469632)) (Checked.append (checkChunk_sound 469760 128 c469760) (checkChunk_sound 469888 128 c469888)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 470016 128 c470016) (checkChunk_sound 470144 128 c470144)) (Checked.append (checkChunk_sound 470272 128 c470272) (checkChunk_sound 470400 128 c470400))) (Checked.append (Checked.append (checkChunk_sound 470528 128 c470528) (checkChunk_sound 470656 128 c470656)) (Checked.append (checkChunk_sound 470784 128 c470784) (checkChunk_sound 470912 128 c470912)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 471040 128 c471040) (checkChunk_sound 471168 128 c471168)) (Checked.append (checkChunk_sound 471296 128 c471296) (checkChunk_sound 471424 128 c471424))) (Checked.append (Checked.append (checkChunk_sound 471552 128 c471552) (checkChunk_sound 471680 128 c471680)) (Checked.append (checkChunk_sound 471808 128 c471808) (checkChunk_sound 471936 128 c471936)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 472064 128 c472064) (checkChunk_sound 472192 128 c472192)) (Checked.append (checkChunk_sound 472320 128 c472320) (checkChunk_sound 472448 128 c472448))) (Checked.append (Checked.append (checkChunk_sound 472576 128 c472576) (checkChunk_sound 472704 128 c472704)) (Checked.append (checkChunk_sound 472832 128 c472832) (checkChunk_sound 472960 128 c472960))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 473088 128 c473088) (checkChunk_sound 473216 128 c473216)) (Checked.append (checkChunk_sound 473344 128 c473344) (checkChunk_sound 473472 128 c473472))) (Checked.append (Checked.append (checkChunk_sound 473600 128 c473600) (checkChunk_sound 473728 128 c473728)) (Checked.append (checkChunk_sound 473856 128 c473856) (checkChunk_sound 473984 128 c473984)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 474112 128 c474112) (checkChunk_sound 474240 128 c474240)) (Checked.append (checkChunk_sound 474368 128 c474368) (checkChunk_sound 474496 128 c474496))) (Checked.append (Checked.append (checkChunk_sound 474624 128 c474624) (checkChunk_sound 474752 128 c474752)) (Checked.append (checkChunk_sound 474880 128 c474880) (checkChunk_sound 475008 128 c475008)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B004
