module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1015808, 1024000).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B019
private theorem c1015808 : checkChunk 1015808 128 = true := by decide +kernel
private theorem c1015936 : checkChunk 1015936 128 = true := by decide +kernel
private theorem c1016064 : checkChunk 1016064 128 = true := by decide +kernel
private theorem c1016192 : checkChunk 1016192 128 = true := by decide +kernel
private theorem c1016320 : checkChunk 1016320 128 = true := by decide +kernel
private theorem c1016448 : checkChunk 1016448 128 = true := by decide +kernel
private theorem c1016576 : checkChunk 1016576 128 = true := by decide +kernel
private theorem c1016704 : checkChunk 1016704 128 = true := by decide +kernel
private theorem c1016832 : checkChunk 1016832 128 = true := by decide +kernel
private theorem c1016960 : checkChunk 1016960 128 = true := by decide +kernel
private theorem c1017088 : checkChunk 1017088 128 = true := by decide +kernel
private theorem c1017216 : checkChunk 1017216 128 = true := by decide +kernel
private theorem c1017344 : checkChunk 1017344 128 = true := by decide +kernel
private theorem c1017472 : checkChunk 1017472 128 = true := by decide +kernel
private theorem c1017600 : checkChunk 1017600 128 = true := by decide +kernel
private theorem c1017728 : checkChunk 1017728 128 = true := by decide +kernel
private theorem c1017856 : checkChunk 1017856 128 = true := by decide +kernel
private theorem c1017984 : checkChunk 1017984 128 = true := by decide +kernel
private theorem c1018112 : checkChunk 1018112 128 = true := by decide +kernel
private theorem c1018240 : checkChunk 1018240 128 = true := by decide +kernel
private theorem c1018368 : checkChunk 1018368 128 = true := by decide +kernel
private theorem c1018496 : checkChunk 1018496 128 = true := by decide +kernel
private theorem c1018624 : checkChunk 1018624 128 = true := by decide +kernel
private theorem c1018752 : checkChunk 1018752 128 = true := by decide +kernel
private theorem c1018880 : checkChunk 1018880 128 = true := by decide +kernel
private theorem c1019008 : checkChunk 1019008 128 = true := by decide +kernel
private theorem c1019136 : checkChunk 1019136 128 = true := by decide +kernel
private theorem c1019264 : checkChunk 1019264 128 = true := by decide +kernel
private theorem c1019392 : checkChunk 1019392 128 = true := by decide +kernel
private theorem c1019520 : checkChunk 1019520 128 = true := by decide +kernel
private theorem c1019648 : checkChunk 1019648 128 = true := by decide +kernel
private theorem c1019776 : checkChunk 1019776 128 = true := by decide +kernel
private theorem c1019904 : checkChunk 1019904 128 = true := by decide +kernel
private theorem c1020032 : checkChunk 1020032 128 = true := by decide +kernel
private theorem c1020160 : checkChunk 1020160 128 = true := by decide +kernel
private theorem c1020288 : checkChunk 1020288 128 = true := by decide +kernel
private theorem c1020416 : checkChunk 1020416 128 = true := by decide +kernel
private theorem c1020544 : checkChunk 1020544 128 = true := by decide +kernel
private theorem c1020672 : checkChunk 1020672 128 = true := by decide +kernel
private theorem c1020800 : checkChunk 1020800 128 = true := by decide +kernel
private theorem c1020928 : checkChunk 1020928 128 = true := by decide +kernel
private theorem c1021056 : checkChunk 1021056 128 = true := by decide +kernel
private theorem c1021184 : checkChunk 1021184 128 = true := by decide +kernel
private theorem c1021312 : checkChunk 1021312 128 = true := by decide +kernel
private theorem c1021440 : checkChunk 1021440 128 = true := by decide +kernel
private theorem c1021568 : checkChunk 1021568 128 = true := by decide +kernel
private theorem c1021696 : checkChunk 1021696 128 = true := by decide +kernel
private theorem c1021824 : checkChunk 1021824 128 = true := by decide +kernel
private theorem c1021952 : checkChunk 1021952 128 = true := by decide +kernel
private theorem c1022080 : checkChunk 1022080 128 = true := by decide +kernel
private theorem c1022208 : checkChunk 1022208 128 = true := by decide +kernel
private theorem c1022336 : checkChunk 1022336 128 = true := by decide +kernel
private theorem c1022464 : checkChunk 1022464 128 = true := by decide +kernel
private theorem c1022592 : checkChunk 1022592 128 = true := by decide +kernel
private theorem c1022720 : checkChunk 1022720 128 = true := by decide +kernel
private theorem c1022848 : checkChunk 1022848 128 = true := by decide +kernel
private theorem c1022976 : checkChunk 1022976 128 = true := by decide +kernel
private theorem c1023104 : checkChunk 1023104 128 = true := by decide +kernel
private theorem c1023232 : checkChunk 1023232 128 = true := by decide +kernel
private theorem c1023360 : checkChunk 1023360 128 = true := by decide +kernel
private theorem c1023488 : checkChunk 1023488 128 = true := by decide +kernel
private theorem c1023616 : checkChunk 1023616 128 = true := by decide +kernel
private theorem c1023744 : checkChunk 1023744 128 = true := by decide +kernel
private theorem c1023872 : checkChunk 1023872 128 = true := by decide +kernel

public theorem checked : Checked 1015808 1024000 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1015808 128 c1015808) (checkChunk_sound 1015936 128 c1015936)) (Checked.append (checkChunk_sound 1016064 128 c1016064) (checkChunk_sound 1016192 128 c1016192))) (Checked.append (Checked.append (checkChunk_sound 1016320 128 c1016320) (checkChunk_sound 1016448 128 c1016448)) (Checked.append (checkChunk_sound 1016576 128 c1016576) (checkChunk_sound 1016704 128 c1016704)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1016832 128 c1016832) (checkChunk_sound 1016960 128 c1016960)) (Checked.append (checkChunk_sound 1017088 128 c1017088) (checkChunk_sound 1017216 128 c1017216))) (Checked.append (Checked.append (checkChunk_sound 1017344 128 c1017344) (checkChunk_sound 1017472 128 c1017472)) (Checked.append (checkChunk_sound 1017600 128 c1017600) (checkChunk_sound 1017728 128 c1017728))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1017856 128 c1017856) (checkChunk_sound 1017984 128 c1017984)) (Checked.append (checkChunk_sound 1018112 128 c1018112) (checkChunk_sound 1018240 128 c1018240))) (Checked.append (Checked.append (checkChunk_sound 1018368 128 c1018368) (checkChunk_sound 1018496 128 c1018496)) (Checked.append (checkChunk_sound 1018624 128 c1018624) (checkChunk_sound 1018752 128 c1018752)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1018880 128 c1018880) (checkChunk_sound 1019008 128 c1019008)) (Checked.append (checkChunk_sound 1019136 128 c1019136) (checkChunk_sound 1019264 128 c1019264))) (Checked.append (Checked.append (checkChunk_sound 1019392 128 c1019392) (checkChunk_sound 1019520 128 c1019520)) (Checked.append (checkChunk_sound 1019648 128 c1019648) (checkChunk_sound 1019776 128 c1019776)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1019904 128 c1019904) (checkChunk_sound 1020032 128 c1020032)) (Checked.append (checkChunk_sound 1020160 128 c1020160) (checkChunk_sound 1020288 128 c1020288))) (Checked.append (Checked.append (checkChunk_sound 1020416 128 c1020416) (checkChunk_sound 1020544 128 c1020544)) (Checked.append (checkChunk_sound 1020672 128 c1020672) (checkChunk_sound 1020800 128 c1020800)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1020928 128 c1020928) (checkChunk_sound 1021056 128 c1021056)) (Checked.append (checkChunk_sound 1021184 128 c1021184) (checkChunk_sound 1021312 128 c1021312))) (Checked.append (Checked.append (checkChunk_sound 1021440 128 c1021440) (checkChunk_sound 1021568 128 c1021568)) (Checked.append (checkChunk_sound 1021696 128 c1021696) (checkChunk_sound 1021824 128 c1021824))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1021952 128 c1021952) (checkChunk_sound 1022080 128 c1022080)) (Checked.append (checkChunk_sound 1022208 128 c1022208) (checkChunk_sound 1022336 128 c1022336))) (Checked.append (Checked.append (checkChunk_sound 1022464 128 c1022464) (checkChunk_sound 1022592 128 c1022592)) (Checked.append (checkChunk_sound 1022720 128 c1022720) (checkChunk_sound 1022848 128 c1022848)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1022976 128 c1022976) (checkChunk_sound 1023104 128 c1023104)) (Checked.append (checkChunk_sound 1023232 128 c1023232) (checkChunk_sound 1023360 128 c1023360))) (Checked.append (Checked.append (checkChunk_sound 1023488 128 c1023488) (checkChunk_sound 1023616 128 c1023616)) (Checked.append (checkChunk_sound 1023744 128 c1023744) (checkChunk_sound 1023872 128 c1023872)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B019
