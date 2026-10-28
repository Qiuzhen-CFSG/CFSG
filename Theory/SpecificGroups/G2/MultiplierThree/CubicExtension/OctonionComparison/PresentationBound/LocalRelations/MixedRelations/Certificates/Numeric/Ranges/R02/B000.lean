module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [434176, 442368).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B000
private theorem c434176 : checkChunk 434176 128 = true := by decide +kernel
private theorem c434304 : checkChunk 434304 128 = true := by decide +kernel
private theorem c434432 : checkChunk 434432 128 = true := by decide +kernel
private theorem c434560 : checkChunk 434560 128 = true := by decide +kernel
private theorem c434688 : checkChunk 434688 128 = true := by decide +kernel
private theorem c434816 : checkChunk 434816 128 = true := by decide +kernel
private theorem c434944 : checkChunk 434944 128 = true := by decide +kernel
private theorem c435072 : checkChunk 435072 128 = true := by decide +kernel
private theorem c435200 : checkChunk 435200 128 = true := by decide +kernel
private theorem c435328 : checkChunk 435328 128 = true := by decide +kernel
private theorem c435456 : checkChunk 435456 128 = true := by decide +kernel
private theorem c435584 : checkChunk 435584 128 = true := by decide +kernel
private theorem c435712 : checkChunk 435712 128 = true := by decide +kernel
private theorem c435840 : checkChunk 435840 128 = true := by decide +kernel
private theorem c435968 : checkChunk 435968 128 = true := by decide +kernel
private theorem c436096 : checkChunk 436096 128 = true := by decide +kernel
private theorem c436224 : checkChunk 436224 128 = true := by decide +kernel
private theorem c436352 : checkChunk 436352 128 = true := by decide +kernel
private theorem c436480 : checkChunk 436480 128 = true := by decide +kernel
private theorem c436608 : checkChunk 436608 128 = true := by decide +kernel
private theorem c436736 : checkChunk 436736 128 = true := by decide +kernel
private theorem c436864 : checkChunk 436864 128 = true := by decide +kernel
private theorem c436992 : checkChunk 436992 128 = true := by decide +kernel
private theorem c437120 : checkChunk 437120 128 = true := by decide +kernel
private theorem c437248 : checkChunk 437248 128 = true := by decide +kernel
private theorem c437376 : checkChunk 437376 128 = true := by decide +kernel
private theorem c437504 : checkChunk 437504 128 = true := by decide +kernel
private theorem c437632 : checkChunk 437632 128 = true := by decide +kernel
private theorem c437760 : checkChunk 437760 128 = true := by decide +kernel
private theorem c437888 : checkChunk 437888 128 = true := by decide +kernel
private theorem c438016 : checkChunk 438016 128 = true := by decide +kernel
private theorem c438144 : checkChunk 438144 128 = true := by decide +kernel
private theorem c438272 : checkChunk 438272 128 = true := by decide +kernel
private theorem c438400 : checkChunk 438400 128 = true := by decide +kernel
private theorem c438528 : checkChunk 438528 128 = true := by decide +kernel
private theorem c438656 : checkChunk 438656 128 = true := by decide +kernel
private theorem c438784 : checkChunk 438784 128 = true := by decide +kernel
private theorem c438912 : checkChunk 438912 128 = true := by decide +kernel
private theorem c439040 : checkChunk 439040 128 = true := by decide +kernel
private theorem c439168 : checkChunk 439168 128 = true := by decide +kernel
private theorem c439296 : checkChunk 439296 128 = true := by decide +kernel
private theorem c439424 : checkChunk 439424 128 = true := by decide +kernel
private theorem c439552 : checkChunk 439552 128 = true := by decide +kernel
private theorem c439680 : checkChunk 439680 128 = true := by decide +kernel
private theorem c439808 : checkChunk 439808 128 = true := by decide +kernel
private theorem c439936 : checkChunk 439936 128 = true := by decide +kernel
private theorem c440064 : checkChunk 440064 128 = true := by decide +kernel
private theorem c440192 : checkChunk 440192 128 = true := by decide +kernel
private theorem c440320 : checkChunk 440320 128 = true := by decide +kernel
private theorem c440448 : checkChunk 440448 128 = true := by decide +kernel
private theorem c440576 : checkChunk 440576 128 = true := by decide +kernel
private theorem c440704 : checkChunk 440704 128 = true := by decide +kernel
private theorem c440832 : checkChunk 440832 128 = true := by decide +kernel
private theorem c440960 : checkChunk 440960 128 = true := by decide +kernel
private theorem c441088 : checkChunk 441088 128 = true := by decide +kernel
private theorem c441216 : checkChunk 441216 128 = true := by decide +kernel
private theorem c441344 : checkChunk 441344 128 = true := by decide +kernel
private theorem c441472 : checkChunk 441472 128 = true := by decide +kernel
private theorem c441600 : checkChunk 441600 128 = true := by decide +kernel
private theorem c441728 : checkChunk 441728 128 = true := by decide +kernel
private theorem c441856 : checkChunk 441856 128 = true := by decide +kernel
private theorem c441984 : checkChunk 441984 128 = true := by decide +kernel
private theorem c442112 : checkChunk 442112 128 = true := by decide +kernel
private theorem c442240 : checkChunk 442240 128 = true := by decide +kernel

public theorem checked : Checked 434176 442368 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 434176 128 c434176) (checkChunk_sound 434304 128 c434304)) (Checked.append (checkChunk_sound 434432 128 c434432) (checkChunk_sound 434560 128 c434560))) (Checked.append (Checked.append (checkChunk_sound 434688 128 c434688) (checkChunk_sound 434816 128 c434816)) (Checked.append (checkChunk_sound 434944 128 c434944) (checkChunk_sound 435072 128 c435072)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 435200 128 c435200) (checkChunk_sound 435328 128 c435328)) (Checked.append (checkChunk_sound 435456 128 c435456) (checkChunk_sound 435584 128 c435584))) (Checked.append (Checked.append (checkChunk_sound 435712 128 c435712) (checkChunk_sound 435840 128 c435840)) (Checked.append (checkChunk_sound 435968 128 c435968) (checkChunk_sound 436096 128 c436096))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 436224 128 c436224) (checkChunk_sound 436352 128 c436352)) (Checked.append (checkChunk_sound 436480 128 c436480) (checkChunk_sound 436608 128 c436608))) (Checked.append (Checked.append (checkChunk_sound 436736 128 c436736) (checkChunk_sound 436864 128 c436864)) (Checked.append (checkChunk_sound 436992 128 c436992) (checkChunk_sound 437120 128 c437120)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 437248 128 c437248) (checkChunk_sound 437376 128 c437376)) (Checked.append (checkChunk_sound 437504 128 c437504) (checkChunk_sound 437632 128 c437632))) (Checked.append (Checked.append (checkChunk_sound 437760 128 c437760) (checkChunk_sound 437888 128 c437888)) (Checked.append (checkChunk_sound 438016 128 c438016) (checkChunk_sound 438144 128 c438144)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 438272 128 c438272) (checkChunk_sound 438400 128 c438400)) (Checked.append (checkChunk_sound 438528 128 c438528) (checkChunk_sound 438656 128 c438656))) (Checked.append (Checked.append (checkChunk_sound 438784 128 c438784) (checkChunk_sound 438912 128 c438912)) (Checked.append (checkChunk_sound 439040 128 c439040) (checkChunk_sound 439168 128 c439168)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 439296 128 c439296) (checkChunk_sound 439424 128 c439424)) (Checked.append (checkChunk_sound 439552 128 c439552) (checkChunk_sound 439680 128 c439680))) (Checked.append (Checked.append (checkChunk_sound 439808 128 c439808) (checkChunk_sound 439936 128 c439936)) (Checked.append (checkChunk_sound 440064 128 c440064) (checkChunk_sound 440192 128 c440192))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 440320 128 c440320) (checkChunk_sound 440448 128 c440448)) (Checked.append (checkChunk_sound 440576 128 c440576) (checkChunk_sound 440704 128 c440704))) (Checked.append (Checked.append (checkChunk_sound 440832 128 c440832) (checkChunk_sound 440960 128 c440960)) (Checked.append (checkChunk_sound 441088 128 c441088) (checkChunk_sound 441216 128 c441216)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 441344 128 c441344) (checkChunk_sound 441472 128 c441472)) (Checked.append (checkChunk_sound 441600 128 c441600) (checkChunk_sound 441728 128 c441728))) (Checked.append (Checked.append (checkChunk_sound 441856 128 c441856) (checkChunk_sound 441984 128 c441984)) (Checked.append (checkChunk_sound 442112 128 c442112) (checkChunk_sound 442240 128 c442240)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B000
