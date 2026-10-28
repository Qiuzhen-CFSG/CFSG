module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [753664, 761856).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B013
private theorem c753664 : checkChunk 753664 128 = true := by decide +kernel
private theorem c753792 : checkChunk 753792 128 = true := by decide +kernel
private theorem c753920 : checkChunk 753920 128 = true := by decide +kernel
private theorem c754048 : checkChunk 754048 128 = true := by decide +kernel
private theorem c754176 : checkChunk 754176 128 = true := by decide +kernel
private theorem c754304 : checkChunk 754304 128 = true := by decide +kernel
private theorem c754432 : checkChunk 754432 128 = true := by decide +kernel
private theorem c754560 : checkChunk 754560 128 = true := by decide +kernel
private theorem c754688 : checkChunk 754688 128 = true := by decide +kernel
private theorem c754816 : checkChunk 754816 128 = true := by decide +kernel
private theorem c754944 : checkChunk 754944 128 = true := by decide +kernel
private theorem c755072 : checkChunk 755072 128 = true := by decide +kernel
private theorem c755200 : checkChunk 755200 128 = true := by decide +kernel
private theorem c755328 : checkChunk 755328 128 = true := by decide +kernel
private theorem c755456 : checkChunk 755456 128 = true := by decide +kernel
private theorem c755584 : checkChunk 755584 128 = true := by decide +kernel
private theorem c755712 : checkChunk 755712 128 = true := by decide +kernel
private theorem c755840 : checkChunk 755840 128 = true := by decide +kernel
private theorem c755968 : checkChunk 755968 128 = true := by decide +kernel
private theorem c756096 : checkChunk 756096 128 = true := by decide +kernel
private theorem c756224 : checkChunk 756224 128 = true := by decide +kernel
private theorem c756352 : checkChunk 756352 128 = true := by decide +kernel
private theorem c756480 : checkChunk 756480 128 = true := by decide +kernel
private theorem c756608 : checkChunk 756608 128 = true := by decide +kernel
private theorem c756736 : checkChunk 756736 128 = true := by decide +kernel
private theorem c756864 : checkChunk 756864 128 = true := by decide +kernel
private theorem c756992 : checkChunk 756992 128 = true := by decide +kernel
private theorem c757120 : checkChunk 757120 128 = true := by decide +kernel
private theorem c757248 : checkChunk 757248 128 = true := by decide +kernel
private theorem c757376 : checkChunk 757376 128 = true := by decide +kernel
private theorem c757504 : checkChunk 757504 128 = true := by decide +kernel
private theorem c757632 : checkChunk 757632 128 = true := by decide +kernel
private theorem c757760 : checkChunk 757760 128 = true := by decide +kernel
private theorem c757888 : checkChunk 757888 128 = true := by decide +kernel
private theorem c758016 : checkChunk 758016 128 = true := by decide +kernel
private theorem c758144 : checkChunk 758144 128 = true := by decide +kernel
private theorem c758272 : checkChunk 758272 128 = true := by decide +kernel
private theorem c758400 : checkChunk 758400 128 = true := by decide +kernel
private theorem c758528 : checkChunk 758528 128 = true := by decide +kernel
private theorem c758656 : checkChunk 758656 128 = true := by decide +kernel
private theorem c758784 : checkChunk 758784 128 = true := by decide +kernel
private theorem c758912 : checkChunk 758912 128 = true := by decide +kernel
private theorem c759040 : checkChunk 759040 128 = true := by decide +kernel
private theorem c759168 : checkChunk 759168 128 = true := by decide +kernel
private theorem c759296 : checkChunk 759296 128 = true := by decide +kernel
private theorem c759424 : checkChunk 759424 128 = true := by decide +kernel
private theorem c759552 : checkChunk 759552 128 = true := by decide +kernel
private theorem c759680 : checkChunk 759680 128 = true := by decide +kernel
private theorem c759808 : checkChunk 759808 128 = true := by decide +kernel
private theorem c759936 : checkChunk 759936 128 = true := by decide +kernel
private theorem c760064 : checkChunk 760064 128 = true := by decide +kernel
private theorem c760192 : checkChunk 760192 128 = true := by decide +kernel
private theorem c760320 : checkChunk 760320 128 = true := by decide +kernel
private theorem c760448 : checkChunk 760448 128 = true := by decide +kernel
private theorem c760576 : checkChunk 760576 128 = true := by decide +kernel
private theorem c760704 : checkChunk 760704 128 = true := by decide +kernel
private theorem c760832 : checkChunk 760832 128 = true := by decide +kernel
private theorem c760960 : checkChunk 760960 128 = true := by decide +kernel
private theorem c761088 : checkChunk 761088 128 = true := by decide +kernel
private theorem c761216 : checkChunk 761216 128 = true := by decide +kernel
private theorem c761344 : checkChunk 761344 128 = true := by decide +kernel
private theorem c761472 : checkChunk 761472 128 = true := by decide +kernel
private theorem c761600 : checkChunk 761600 128 = true := by decide +kernel
private theorem c761728 : checkChunk 761728 128 = true := by decide +kernel

public theorem checked : Checked 753664 761856 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 753664 128 c753664) (checkChunk_sound 753792 128 c753792)) (Checked.append (checkChunk_sound 753920 128 c753920) (checkChunk_sound 754048 128 c754048))) (Checked.append (Checked.append (checkChunk_sound 754176 128 c754176) (checkChunk_sound 754304 128 c754304)) (Checked.append (checkChunk_sound 754432 128 c754432) (checkChunk_sound 754560 128 c754560)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 754688 128 c754688) (checkChunk_sound 754816 128 c754816)) (Checked.append (checkChunk_sound 754944 128 c754944) (checkChunk_sound 755072 128 c755072))) (Checked.append (Checked.append (checkChunk_sound 755200 128 c755200) (checkChunk_sound 755328 128 c755328)) (Checked.append (checkChunk_sound 755456 128 c755456) (checkChunk_sound 755584 128 c755584))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 755712 128 c755712) (checkChunk_sound 755840 128 c755840)) (Checked.append (checkChunk_sound 755968 128 c755968) (checkChunk_sound 756096 128 c756096))) (Checked.append (Checked.append (checkChunk_sound 756224 128 c756224) (checkChunk_sound 756352 128 c756352)) (Checked.append (checkChunk_sound 756480 128 c756480) (checkChunk_sound 756608 128 c756608)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 756736 128 c756736) (checkChunk_sound 756864 128 c756864)) (Checked.append (checkChunk_sound 756992 128 c756992) (checkChunk_sound 757120 128 c757120))) (Checked.append (Checked.append (checkChunk_sound 757248 128 c757248) (checkChunk_sound 757376 128 c757376)) (Checked.append (checkChunk_sound 757504 128 c757504) (checkChunk_sound 757632 128 c757632)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 757760 128 c757760) (checkChunk_sound 757888 128 c757888)) (Checked.append (checkChunk_sound 758016 128 c758016) (checkChunk_sound 758144 128 c758144))) (Checked.append (Checked.append (checkChunk_sound 758272 128 c758272) (checkChunk_sound 758400 128 c758400)) (Checked.append (checkChunk_sound 758528 128 c758528) (checkChunk_sound 758656 128 c758656)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 758784 128 c758784) (checkChunk_sound 758912 128 c758912)) (Checked.append (checkChunk_sound 759040 128 c759040) (checkChunk_sound 759168 128 c759168))) (Checked.append (Checked.append (checkChunk_sound 759296 128 c759296) (checkChunk_sound 759424 128 c759424)) (Checked.append (checkChunk_sound 759552 128 c759552) (checkChunk_sound 759680 128 c759680))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 759808 128 c759808) (checkChunk_sound 759936 128 c759936)) (Checked.append (checkChunk_sound 760064 128 c760064) (checkChunk_sound 760192 128 c760192))) (Checked.append (Checked.append (checkChunk_sound 760320 128 c760320) (checkChunk_sound 760448 128 c760448)) (Checked.append (checkChunk_sound 760576 128 c760576) (checkChunk_sound 760704 128 c760704)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 760832 128 c760832) (checkChunk_sound 760960 128 c760960)) (Checked.append (checkChunk_sound 761088 128 c761088) (checkChunk_sound 761216 128 c761216))) (Checked.append (Checked.append (checkChunk_sound 761344 128 c761344) (checkChunk_sound 761472 128 c761472)) (Checked.append (checkChunk_sound 761600 128 c761600) (checkChunk_sound 761728 128 c761728)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B013
