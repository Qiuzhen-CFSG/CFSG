module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [786432, 794624).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B017
private theorem c786432 : checkChunk 786432 128 = true := by decide +kernel
private theorem c786560 : checkChunk 786560 128 = true := by decide +kernel
private theorem c786688 : checkChunk 786688 128 = true := by decide +kernel
private theorem c786816 : checkChunk 786816 128 = true := by decide +kernel
private theorem c786944 : checkChunk 786944 128 = true := by decide +kernel
private theorem c787072 : checkChunk 787072 128 = true := by decide +kernel
private theorem c787200 : checkChunk 787200 128 = true := by decide +kernel
private theorem c787328 : checkChunk 787328 128 = true := by decide +kernel
private theorem c787456 : checkChunk 787456 128 = true := by decide +kernel
private theorem c787584 : checkChunk 787584 128 = true := by decide +kernel
private theorem c787712 : checkChunk 787712 128 = true := by decide +kernel
private theorem c787840 : checkChunk 787840 128 = true := by decide +kernel
private theorem c787968 : checkChunk 787968 128 = true := by decide +kernel
private theorem c788096 : checkChunk 788096 128 = true := by decide +kernel
private theorem c788224 : checkChunk 788224 128 = true := by decide +kernel
private theorem c788352 : checkChunk 788352 128 = true := by decide +kernel
private theorem c788480 : checkChunk 788480 128 = true := by decide +kernel
private theorem c788608 : checkChunk 788608 128 = true := by decide +kernel
private theorem c788736 : checkChunk 788736 128 = true := by decide +kernel
private theorem c788864 : checkChunk 788864 128 = true := by decide +kernel
private theorem c788992 : checkChunk 788992 128 = true := by decide +kernel
private theorem c789120 : checkChunk 789120 128 = true := by decide +kernel
private theorem c789248 : checkChunk 789248 128 = true := by decide +kernel
private theorem c789376 : checkChunk 789376 128 = true := by decide +kernel
private theorem c789504 : checkChunk 789504 128 = true := by decide +kernel
private theorem c789632 : checkChunk 789632 128 = true := by decide +kernel
private theorem c789760 : checkChunk 789760 128 = true := by decide +kernel
private theorem c789888 : checkChunk 789888 128 = true := by decide +kernel
private theorem c790016 : checkChunk 790016 128 = true := by decide +kernel
private theorem c790144 : checkChunk 790144 128 = true := by decide +kernel
private theorem c790272 : checkChunk 790272 128 = true := by decide +kernel
private theorem c790400 : checkChunk 790400 128 = true := by decide +kernel
private theorem c790528 : checkChunk 790528 128 = true := by decide +kernel
private theorem c790656 : checkChunk 790656 128 = true := by decide +kernel
private theorem c790784 : checkChunk 790784 128 = true := by decide +kernel
private theorem c790912 : checkChunk 790912 128 = true := by decide +kernel
private theorem c791040 : checkChunk 791040 128 = true := by decide +kernel
private theorem c791168 : checkChunk 791168 128 = true := by decide +kernel
private theorem c791296 : checkChunk 791296 128 = true := by decide +kernel
private theorem c791424 : checkChunk 791424 128 = true := by decide +kernel
private theorem c791552 : checkChunk 791552 128 = true := by decide +kernel
private theorem c791680 : checkChunk 791680 128 = true := by decide +kernel
private theorem c791808 : checkChunk 791808 128 = true := by decide +kernel
private theorem c791936 : checkChunk 791936 128 = true := by decide +kernel
private theorem c792064 : checkChunk 792064 128 = true := by decide +kernel
private theorem c792192 : checkChunk 792192 128 = true := by decide +kernel
private theorem c792320 : checkChunk 792320 128 = true := by decide +kernel
private theorem c792448 : checkChunk 792448 128 = true := by decide +kernel
private theorem c792576 : checkChunk 792576 128 = true := by decide +kernel
private theorem c792704 : checkChunk 792704 128 = true := by decide +kernel
private theorem c792832 : checkChunk 792832 128 = true := by decide +kernel
private theorem c792960 : checkChunk 792960 128 = true := by decide +kernel
private theorem c793088 : checkChunk 793088 128 = true := by decide +kernel
private theorem c793216 : checkChunk 793216 128 = true := by decide +kernel
private theorem c793344 : checkChunk 793344 128 = true := by decide +kernel
private theorem c793472 : checkChunk 793472 128 = true := by decide +kernel
private theorem c793600 : checkChunk 793600 128 = true := by decide +kernel
private theorem c793728 : checkChunk 793728 128 = true := by decide +kernel
private theorem c793856 : checkChunk 793856 128 = true := by decide +kernel
private theorem c793984 : checkChunk 793984 128 = true := by decide +kernel
private theorem c794112 : checkChunk 794112 128 = true := by decide +kernel
private theorem c794240 : checkChunk 794240 128 = true := by decide +kernel
private theorem c794368 : checkChunk 794368 128 = true := by decide +kernel
private theorem c794496 : checkChunk 794496 128 = true := by decide +kernel

public theorem checked : Checked 786432 794624 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 786432 128 c786432) (checkChunk_sound 786560 128 c786560)) (Checked.append (checkChunk_sound 786688 128 c786688) (checkChunk_sound 786816 128 c786816))) (Checked.append (Checked.append (checkChunk_sound 786944 128 c786944) (checkChunk_sound 787072 128 c787072)) (Checked.append (checkChunk_sound 787200 128 c787200) (checkChunk_sound 787328 128 c787328)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 787456 128 c787456) (checkChunk_sound 787584 128 c787584)) (Checked.append (checkChunk_sound 787712 128 c787712) (checkChunk_sound 787840 128 c787840))) (Checked.append (Checked.append (checkChunk_sound 787968 128 c787968) (checkChunk_sound 788096 128 c788096)) (Checked.append (checkChunk_sound 788224 128 c788224) (checkChunk_sound 788352 128 c788352))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 788480 128 c788480) (checkChunk_sound 788608 128 c788608)) (Checked.append (checkChunk_sound 788736 128 c788736) (checkChunk_sound 788864 128 c788864))) (Checked.append (Checked.append (checkChunk_sound 788992 128 c788992) (checkChunk_sound 789120 128 c789120)) (Checked.append (checkChunk_sound 789248 128 c789248) (checkChunk_sound 789376 128 c789376)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 789504 128 c789504) (checkChunk_sound 789632 128 c789632)) (Checked.append (checkChunk_sound 789760 128 c789760) (checkChunk_sound 789888 128 c789888))) (Checked.append (Checked.append (checkChunk_sound 790016 128 c790016) (checkChunk_sound 790144 128 c790144)) (Checked.append (checkChunk_sound 790272 128 c790272) (checkChunk_sound 790400 128 c790400)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 790528 128 c790528) (checkChunk_sound 790656 128 c790656)) (Checked.append (checkChunk_sound 790784 128 c790784) (checkChunk_sound 790912 128 c790912))) (Checked.append (Checked.append (checkChunk_sound 791040 128 c791040) (checkChunk_sound 791168 128 c791168)) (Checked.append (checkChunk_sound 791296 128 c791296) (checkChunk_sound 791424 128 c791424)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 791552 128 c791552) (checkChunk_sound 791680 128 c791680)) (Checked.append (checkChunk_sound 791808 128 c791808) (checkChunk_sound 791936 128 c791936))) (Checked.append (Checked.append (checkChunk_sound 792064 128 c792064) (checkChunk_sound 792192 128 c792192)) (Checked.append (checkChunk_sound 792320 128 c792320) (checkChunk_sound 792448 128 c792448))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 792576 128 c792576) (checkChunk_sound 792704 128 c792704)) (Checked.append (checkChunk_sound 792832 128 c792832) (checkChunk_sound 792960 128 c792960))) (Checked.append (Checked.append (checkChunk_sound 793088 128 c793088) (checkChunk_sound 793216 128 c793216)) (Checked.append (checkChunk_sound 793344 128 c793344) (checkChunk_sound 793472 128 c793472)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 793600 128 c793600) (checkChunk_sound 793728 128 c793728)) (Checked.append (checkChunk_sound 793856 128 c793856) (checkChunk_sound 793984 128 c793984))) (Checked.append (Checked.append (checkChunk_sound 794112 128 c794112) (checkChunk_sound 794240 128 c794240)) (Checked.append (checkChunk_sound 794368 128 c794368) (checkChunk_sound 794496 128 c794496)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B017
