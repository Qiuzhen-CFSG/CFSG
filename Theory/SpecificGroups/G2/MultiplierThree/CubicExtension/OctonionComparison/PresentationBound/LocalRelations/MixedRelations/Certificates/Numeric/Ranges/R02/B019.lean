module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [589824, 598016).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B019
private theorem c589824 : checkChunk 589824 128 = true := by decide +kernel
private theorem c589952 : checkChunk 589952 128 = true := by decide +kernel
private theorem c590080 : checkChunk 590080 128 = true := by decide +kernel
private theorem c590208 : checkChunk 590208 128 = true := by decide +kernel
private theorem c590336 : checkChunk 590336 128 = true := by decide +kernel
private theorem c590464 : checkChunk 590464 128 = true := by decide +kernel
private theorem c590592 : checkChunk 590592 128 = true := by decide +kernel
private theorem c590720 : checkChunk 590720 128 = true := by decide +kernel
private theorem c590848 : checkChunk 590848 128 = true := by decide +kernel
private theorem c590976 : checkChunk 590976 128 = true := by decide +kernel
private theorem c591104 : checkChunk 591104 128 = true := by decide +kernel
private theorem c591232 : checkChunk 591232 128 = true := by decide +kernel
private theorem c591360 : checkChunk 591360 128 = true := by decide +kernel
private theorem c591488 : checkChunk 591488 128 = true := by decide +kernel
private theorem c591616 : checkChunk 591616 128 = true := by decide +kernel
private theorem c591744 : checkChunk 591744 128 = true := by decide +kernel
private theorem c591872 : checkChunk 591872 128 = true := by decide +kernel
private theorem c592000 : checkChunk 592000 128 = true := by decide +kernel
private theorem c592128 : checkChunk 592128 128 = true := by decide +kernel
private theorem c592256 : checkChunk 592256 128 = true := by decide +kernel
private theorem c592384 : checkChunk 592384 128 = true := by decide +kernel
private theorem c592512 : checkChunk 592512 128 = true := by decide +kernel
private theorem c592640 : checkChunk 592640 128 = true := by decide +kernel
private theorem c592768 : checkChunk 592768 128 = true := by decide +kernel
private theorem c592896 : checkChunk 592896 128 = true := by decide +kernel
private theorem c593024 : checkChunk 593024 128 = true := by decide +kernel
private theorem c593152 : checkChunk 593152 128 = true := by decide +kernel
private theorem c593280 : checkChunk 593280 128 = true := by decide +kernel
private theorem c593408 : checkChunk 593408 128 = true := by decide +kernel
private theorem c593536 : checkChunk 593536 128 = true := by decide +kernel
private theorem c593664 : checkChunk 593664 128 = true := by decide +kernel
private theorem c593792 : checkChunk 593792 128 = true := by decide +kernel
private theorem c593920 : checkChunk 593920 128 = true := by decide +kernel
private theorem c594048 : checkChunk 594048 128 = true := by decide +kernel
private theorem c594176 : checkChunk 594176 128 = true := by decide +kernel
private theorem c594304 : checkChunk 594304 128 = true := by decide +kernel
private theorem c594432 : checkChunk 594432 128 = true := by decide +kernel
private theorem c594560 : checkChunk 594560 128 = true := by decide +kernel
private theorem c594688 : checkChunk 594688 128 = true := by decide +kernel
private theorem c594816 : checkChunk 594816 128 = true := by decide +kernel
private theorem c594944 : checkChunk 594944 128 = true := by decide +kernel
private theorem c595072 : checkChunk 595072 128 = true := by decide +kernel
private theorem c595200 : checkChunk 595200 128 = true := by decide +kernel
private theorem c595328 : checkChunk 595328 128 = true := by decide +kernel
private theorem c595456 : checkChunk 595456 128 = true := by decide +kernel
private theorem c595584 : checkChunk 595584 128 = true := by decide +kernel
private theorem c595712 : checkChunk 595712 128 = true := by decide +kernel
private theorem c595840 : checkChunk 595840 128 = true := by decide +kernel
private theorem c595968 : checkChunk 595968 128 = true := by decide +kernel
private theorem c596096 : checkChunk 596096 128 = true := by decide +kernel
private theorem c596224 : checkChunk 596224 128 = true := by decide +kernel
private theorem c596352 : checkChunk 596352 128 = true := by decide +kernel
private theorem c596480 : checkChunk 596480 128 = true := by decide +kernel
private theorem c596608 : checkChunk 596608 128 = true := by decide +kernel
private theorem c596736 : checkChunk 596736 128 = true := by decide +kernel
private theorem c596864 : checkChunk 596864 128 = true := by decide +kernel
private theorem c596992 : checkChunk 596992 128 = true := by decide +kernel
private theorem c597120 : checkChunk 597120 128 = true := by decide +kernel
private theorem c597248 : checkChunk 597248 128 = true := by decide +kernel
private theorem c597376 : checkChunk 597376 128 = true := by decide +kernel
private theorem c597504 : checkChunk 597504 128 = true := by decide +kernel
private theorem c597632 : checkChunk 597632 128 = true := by decide +kernel
private theorem c597760 : checkChunk 597760 128 = true := by decide +kernel
private theorem c597888 : checkChunk 597888 128 = true := by decide +kernel

public theorem checked : Checked 589824 598016 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 589824 128 c589824) (checkChunk_sound 589952 128 c589952)) (Checked.append (checkChunk_sound 590080 128 c590080) (checkChunk_sound 590208 128 c590208))) (Checked.append (Checked.append (checkChunk_sound 590336 128 c590336) (checkChunk_sound 590464 128 c590464)) (Checked.append (checkChunk_sound 590592 128 c590592) (checkChunk_sound 590720 128 c590720)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 590848 128 c590848) (checkChunk_sound 590976 128 c590976)) (Checked.append (checkChunk_sound 591104 128 c591104) (checkChunk_sound 591232 128 c591232))) (Checked.append (Checked.append (checkChunk_sound 591360 128 c591360) (checkChunk_sound 591488 128 c591488)) (Checked.append (checkChunk_sound 591616 128 c591616) (checkChunk_sound 591744 128 c591744))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 591872 128 c591872) (checkChunk_sound 592000 128 c592000)) (Checked.append (checkChunk_sound 592128 128 c592128) (checkChunk_sound 592256 128 c592256))) (Checked.append (Checked.append (checkChunk_sound 592384 128 c592384) (checkChunk_sound 592512 128 c592512)) (Checked.append (checkChunk_sound 592640 128 c592640) (checkChunk_sound 592768 128 c592768)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 592896 128 c592896) (checkChunk_sound 593024 128 c593024)) (Checked.append (checkChunk_sound 593152 128 c593152) (checkChunk_sound 593280 128 c593280))) (Checked.append (Checked.append (checkChunk_sound 593408 128 c593408) (checkChunk_sound 593536 128 c593536)) (Checked.append (checkChunk_sound 593664 128 c593664) (checkChunk_sound 593792 128 c593792)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 593920 128 c593920) (checkChunk_sound 594048 128 c594048)) (Checked.append (checkChunk_sound 594176 128 c594176) (checkChunk_sound 594304 128 c594304))) (Checked.append (Checked.append (checkChunk_sound 594432 128 c594432) (checkChunk_sound 594560 128 c594560)) (Checked.append (checkChunk_sound 594688 128 c594688) (checkChunk_sound 594816 128 c594816)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 594944 128 c594944) (checkChunk_sound 595072 128 c595072)) (Checked.append (checkChunk_sound 595200 128 c595200) (checkChunk_sound 595328 128 c595328))) (Checked.append (Checked.append (checkChunk_sound 595456 128 c595456) (checkChunk_sound 595584 128 c595584)) (Checked.append (checkChunk_sound 595712 128 c595712) (checkChunk_sound 595840 128 c595840))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 595968 128 c595968) (checkChunk_sound 596096 128 c596096)) (Checked.append (checkChunk_sound 596224 128 c596224) (checkChunk_sound 596352 128 c596352))) (Checked.append (Checked.append (checkChunk_sound 596480 128 c596480) (checkChunk_sound 596608 128 c596608)) (Checked.append (checkChunk_sound 596736 128 c596736) (checkChunk_sound 596864 128 c596864)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 596992 128 c596992) (checkChunk_sound 597120 128 c597120)) (Checked.append (checkChunk_sound 597248 128 c597248) (checkChunk_sound 597376 128 c597376))) (Checked.append (Checked.append (checkChunk_sound 597504 128 c597504) (checkChunk_sound 597632 128 c597632)) (Checked.append (checkChunk_sound 597760 128 c597760) (checkChunk_sound 597888 128 c597888)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B019
