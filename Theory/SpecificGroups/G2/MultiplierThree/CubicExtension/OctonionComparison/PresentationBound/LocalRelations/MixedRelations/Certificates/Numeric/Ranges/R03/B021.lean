module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [819200, 827392).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B021
private theorem c819200 : checkChunk 819200 128 = true := by decide +kernel
private theorem c819328 : checkChunk 819328 128 = true := by decide +kernel
private theorem c819456 : checkChunk 819456 128 = true := by decide +kernel
private theorem c819584 : checkChunk 819584 128 = true := by decide +kernel
private theorem c819712 : checkChunk 819712 128 = true := by decide +kernel
private theorem c819840 : checkChunk 819840 128 = true := by decide +kernel
private theorem c819968 : checkChunk 819968 128 = true := by decide +kernel
private theorem c820096 : checkChunk 820096 128 = true := by decide +kernel
private theorem c820224 : checkChunk 820224 128 = true := by decide +kernel
private theorem c820352 : checkChunk 820352 128 = true := by decide +kernel
private theorem c820480 : checkChunk 820480 128 = true := by decide +kernel
private theorem c820608 : checkChunk 820608 128 = true := by decide +kernel
private theorem c820736 : checkChunk 820736 128 = true := by decide +kernel
private theorem c820864 : checkChunk 820864 128 = true := by decide +kernel
private theorem c820992 : checkChunk 820992 128 = true := by decide +kernel
private theorem c821120 : checkChunk 821120 128 = true := by decide +kernel
private theorem c821248 : checkChunk 821248 128 = true := by decide +kernel
private theorem c821376 : checkChunk 821376 128 = true := by decide +kernel
private theorem c821504 : checkChunk 821504 128 = true := by decide +kernel
private theorem c821632 : checkChunk 821632 128 = true := by decide +kernel
private theorem c821760 : checkChunk 821760 128 = true := by decide +kernel
private theorem c821888 : checkChunk 821888 128 = true := by decide +kernel
private theorem c822016 : checkChunk 822016 128 = true := by decide +kernel
private theorem c822144 : checkChunk 822144 128 = true := by decide +kernel
private theorem c822272 : checkChunk 822272 128 = true := by decide +kernel
private theorem c822400 : checkChunk 822400 128 = true := by decide +kernel
private theorem c822528 : checkChunk 822528 128 = true := by decide +kernel
private theorem c822656 : checkChunk 822656 128 = true := by decide +kernel
private theorem c822784 : checkChunk 822784 128 = true := by decide +kernel
private theorem c822912 : checkChunk 822912 128 = true := by decide +kernel
private theorem c823040 : checkChunk 823040 128 = true := by decide +kernel
private theorem c823168 : checkChunk 823168 128 = true := by decide +kernel
private theorem c823296 : checkChunk 823296 128 = true := by decide +kernel
private theorem c823424 : checkChunk 823424 128 = true := by decide +kernel
private theorem c823552 : checkChunk 823552 128 = true := by decide +kernel
private theorem c823680 : checkChunk 823680 128 = true := by decide +kernel
private theorem c823808 : checkChunk 823808 128 = true := by decide +kernel
private theorem c823936 : checkChunk 823936 128 = true := by decide +kernel
private theorem c824064 : checkChunk 824064 128 = true := by decide +kernel
private theorem c824192 : checkChunk 824192 128 = true := by decide +kernel
private theorem c824320 : checkChunk 824320 128 = true := by decide +kernel
private theorem c824448 : checkChunk 824448 128 = true := by decide +kernel
private theorem c824576 : checkChunk 824576 128 = true := by decide +kernel
private theorem c824704 : checkChunk 824704 128 = true := by decide +kernel
private theorem c824832 : checkChunk 824832 128 = true := by decide +kernel
private theorem c824960 : checkChunk 824960 128 = true := by decide +kernel
private theorem c825088 : checkChunk 825088 128 = true := by decide +kernel
private theorem c825216 : checkChunk 825216 128 = true := by decide +kernel
private theorem c825344 : checkChunk 825344 128 = true := by decide +kernel
private theorem c825472 : checkChunk 825472 128 = true := by decide +kernel
private theorem c825600 : checkChunk 825600 128 = true := by decide +kernel
private theorem c825728 : checkChunk 825728 128 = true := by decide +kernel
private theorem c825856 : checkChunk 825856 128 = true := by decide +kernel
private theorem c825984 : checkChunk 825984 128 = true := by decide +kernel
private theorem c826112 : checkChunk 826112 128 = true := by decide +kernel
private theorem c826240 : checkChunk 826240 128 = true := by decide +kernel
private theorem c826368 : checkChunk 826368 128 = true := by decide +kernel
private theorem c826496 : checkChunk 826496 128 = true := by decide +kernel
private theorem c826624 : checkChunk 826624 128 = true := by decide +kernel
private theorem c826752 : checkChunk 826752 128 = true := by decide +kernel
private theorem c826880 : checkChunk 826880 128 = true := by decide +kernel
private theorem c827008 : checkChunk 827008 128 = true := by decide +kernel
private theorem c827136 : checkChunk 827136 128 = true := by decide +kernel
private theorem c827264 : checkChunk 827264 128 = true := by decide +kernel

public theorem checked : Checked 819200 827392 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 819200 128 c819200) (checkChunk_sound 819328 128 c819328)) (Checked.append (checkChunk_sound 819456 128 c819456) (checkChunk_sound 819584 128 c819584))) (Checked.append (Checked.append (checkChunk_sound 819712 128 c819712) (checkChunk_sound 819840 128 c819840)) (Checked.append (checkChunk_sound 819968 128 c819968) (checkChunk_sound 820096 128 c820096)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 820224 128 c820224) (checkChunk_sound 820352 128 c820352)) (Checked.append (checkChunk_sound 820480 128 c820480) (checkChunk_sound 820608 128 c820608))) (Checked.append (Checked.append (checkChunk_sound 820736 128 c820736) (checkChunk_sound 820864 128 c820864)) (Checked.append (checkChunk_sound 820992 128 c820992) (checkChunk_sound 821120 128 c821120))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 821248 128 c821248) (checkChunk_sound 821376 128 c821376)) (Checked.append (checkChunk_sound 821504 128 c821504) (checkChunk_sound 821632 128 c821632))) (Checked.append (Checked.append (checkChunk_sound 821760 128 c821760) (checkChunk_sound 821888 128 c821888)) (Checked.append (checkChunk_sound 822016 128 c822016) (checkChunk_sound 822144 128 c822144)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 822272 128 c822272) (checkChunk_sound 822400 128 c822400)) (Checked.append (checkChunk_sound 822528 128 c822528) (checkChunk_sound 822656 128 c822656))) (Checked.append (Checked.append (checkChunk_sound 822784 128 c822784) (checkChunk_sound 822912 128 c822912)) (Checked.append (checkChunk_sound 823040 128 c823040) (checkChunk_sound 823168 128 c823168)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 823296 128 c823296) (checkChunk_sound 823424 128 c823424)) (Checked.append (checkChunk_sound 823552 128 c823552) (checkChunk_sound 823680 128 c823680))) (Checked.append (Checked.append (checkChunk_sound 823808 128 c823808) (checkChunk_sound 823936 128 c823936)) (Checked.append (checkChunk_sound 824064 128 c824064) (checkChunk_sound 824192 128 c824192)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 824320 128 c824320) (checkChunk_sound 824448 128 c824448)) (Checked.append (checkChunk_sound 824576 128 c824576) (checkChunk_sound 824704 128 c824704))) (Checked.append (Checked.append (checkChunk_sound 824832 128 c824832) (checkChunk_sound 824960 128 c824960)) (Checked.append (checkChunk_sound 825088 128 c825088) (checkChunk_sound 825216 128 c825216))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 825344 128 c825344) (checkChunk_sound 825472 128 c825472)) (Checked.append (checkChunk_sound 825600 128 c825600) (checkChunk_sound 825728 128 c825728))) (Checked.append (Checked.append (checkChunk_sound 825856 128 c825856) (checkChunk_sound 825984 128 c825984)) (Checked.append (checkChunk_sound 826112 128 c826112) (checkChunk_sound 826240 128 c826240)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 826368 128 c826368) (checkChunk_sound 826496 128 c826496)) (Checked.append (checkChunk_sound 826624 128 c826624) (checkChunk_sound 826752 128 c826752))) (Checked.append (Checked.append (checkChunk_sound 826880 128 c826880) (checkChunk_sound 827008 128 c827008)) (Checked.append (checkChunk_sound 827136 128 c827136) (checkChunk_sound 827264 128 c827264)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B021
