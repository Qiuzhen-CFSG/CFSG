module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1204224, 1212416).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B016
private theorem c1204224 : checkChunk 1204224 128 = true := by decide +kernel
private theorem c1204352 : checkChunk 1204352 128 = true := by decide +kernel
private theorem c1204480 : checkChunk 1204480 128 = true := by decide +kernel
private theorem c1204608 : checkChunk 1204608 128 = true := by decide +kernel
private theorem c1204736 : checkChunk 1204736 128 = true := by decide +kernel
private theorem c1204864 : checkChunk 1204864 128 = true := by decide +kernel
private theorem c1204992 : checkChunk 1204992 128 = true := by decide +kernel
private theorem c1205120 : checkChunk 1205120 128 = true := by decide +kernel
private theorem c1205248 : checkChunk 1205248 128 = true := by decide +kernel
private theorem c1205376 : checkChunk 1205376 128 = true := by decide +kernel
private theorem c1205504 : checkChunk 1205504 128 = true := by decide +kernel
private theorem c1205632 : checkChunk 1205632 128 = true := by decide +kernel
private theorem c1205760 : checkChunk 1205760 128 = true := by decide +kernel
private theorem c1205888 : checkChunk 1205888 128 = true := by decide +kernel
private theorem c1206016 : checkChunk 1206016 128 = true := by decide +kernel
private theorem c1206144 : checkChunk 1206144 128 = true := by decide +kernel
private theorem c1206272 : checkChunk 1206272 128 = true := by decide +kernel
private theorem c1206400 : checkChunk 1206400 128 = true := by decide +kernel
private theorem c1206528 : checkChunk 1206528 128 = true := by decide +kernel
private theorem c1206656 : checkChunk 1206656 128 = true := by decide +kernel
private theorem c1206784 : checkChunk 1206784 128 = true := by decide +kernel
private theorem c1206912 : checkChunk 1206912 128 = true := by decide +kernel
private theorem c1207040 : checkChunk 1207040 128 = true := by decide +kernel
private theorem c1207168 : checkChunk 1207168 128 = true := by decide +kernel
private theorem c1207296 : checkChunk 1207296 128 = true := by decide +kernel
private theorem c1207424 : checkChunk 1207424 128 = true := by decide +kernel
private theorem c1207552 : checkChunk 1207552 128 = true := by decide +kernel
private theorem c1207680 : checkChunk 1207680 128 = true := by decide +kernel
private theorem c1207808 : checkChunk 1207808 128 = true := by decide +kernel
private theorem c1207936 : checkChunk 1207936 128 = true := by decide +kernel
private theorem c1208064 : checkChunk 1208064 128 = true := by decide +kernel
private theorem c1208192 : checkChunk 1208192 128 = true := by decide +kernel
private theorem c1208320 : checkChunk 1208320 128 = true := by decide +kernel
private theorem c1208448 : checkChunk 1208448 128 = true := by decide +kernel
private theorem c1208576 : checkChunk 1208576 128 = true := by decide +kernel
private theorem c1208704 : checkChunk 1208704 128 = true := by decide +kernel
private theorem c1208832 : checkChunk 1208832 128 = true := by decide +kernel
private theorem c1208960 : checkChunk 1208960 128 = true := by decide +kernel
private theorem c1209088 : checkChunk 1209088 128 = true := by decide +kernel
private theorem c1209216 : checkChunk 1209216 128 = true := by decide +kernel
private theorem c1209344 : checkChunk 1209344 128 = true := by decide +kernel
private theorem c1209472 : checkChunk 1209472 128 = true := by decide +kernel
private theorem c1209600 : checkChunk 1209600 128 = true := by decide +kernel
private theorem c1209728 : checkChunk 1209728 128 = true := by decide +kernel
private theorem c1209856 : checkChunk 1209856 128 = true := by decide +kernel
private theorem c1209984 : checkChunk 1209984 128 = true := by decide +kernel
private theorem c1210112 : checkChunk 1210112 128 = true := by decide +kernel
private theorem c1210240 : checkChunk 1210240 128 = true := by decide +kernel
private theorem c1210368 : checkChunk 1210368 128 = true := by decide +kernel
private theorem c1210496 : checkChunk 1210496 128 = true := by decide +kernel
private theorem c1210624 : checkChunk 1210624 128 = true := by decide +kernel
private theorem c1210752 : checkChunk 1210752 128 = true := by decide +kernel
private theorem c1210880 : checkChunk 1210880 128 = true := by decide +kernel
private theorem c1211008 : checkChunk 1211008 128 = true := by decide +kernel
private theorem c1211136 : checkChunk 1211136 128 = true := by decide +kernel
private theorem c1211264 : checkChunk 1211264 128 = true := by decide +kernel
private theorem c1211392 : checkChunk 1211392 128 = true := by decide +kernel
private theorem c1211520 : checkChunk 1211520 128 = true := by decide +kernel
private theorem c1211648 : checkChunk 1211648 128 = true := by decide +kernel
private theorem c1211776 : checkChunk 1211776 128 = true := by decide +kernel
private theorem c1211904 : checkChunk 1211904 128 = true := by decide +kernel
private theorem c1212032 : checkChunk 1212032 128 = true := by decide +kernel
private theorem c1212160 : checkChunk 1212160 128 = true := by decide +kernel
private theorem c1212288 : checkChunk 1212288 128 = true := by decide +kernel

public theorem checked : Checked 1204224 1212416 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1204224 128 c1204224) (checkChunk_sound 1204352 128 c1204352)) (Checked.append (checkChunk_sound 1204480 128 c1204480) (checkChunk_sound 1204608 128 c1204608))) (Checked.append (Checked.append (checkChunk_sound 1204736 128 c1204736) (checkChunk_sound 1204864 128 c1204864)) (Checked.append (checkChunk_sound 1204992 128 c1204992) (checkChunk_sound 1205120 128 c1205120)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1205248 128 c1205248) (checkChunk_sound 1205376 128 c1205376)) (Checked.append (checkChunk_sound 1205504 128 c1205504) (checkChunk_sound 1205632 128 c1205632))) (Checked.append (Checked.append (checkChunk_sound 1205760 128 c1205760) (checkChunk_sound 1205888 128 c1205888)) (Checked.append (checkChunk_sound 1206016 128 c1206016) (checkChunk_sound 1206144 128 c1206144))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1206272 128 c1206272) (checkChunk_sound 1206400 128 c1206400)) (Checked.append (checkChunk_sound 1206528 128 c1206528) (checkChunk_sound 1206656 128 c1206656))) (Checked.append (Checked.append (checkChunk_sound 1206784 128 c1206784) (checkChunk_sound 1206912 128 c1206912)) (Checked.append (checkChunk_sound 1207040 128 c1207040) (checkChunk_sound 1207168 128 c1207168)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1207296 128 c1207296) (checkChunk_sound 1207424 128 c1207424)) (Checked.append (checkChunk_sound 1207552 128 c1207552) (checkChunk_sound 1207680 128 c1207680))) (Checked.append (Checked.append (checkChunk_sound 1207808 128 c1207808) (checkChunk_sound 1207936 128 c1207936)) (Checked.append (checkChunk_sound 1208064 128 c1208064) (checkChunk_sound 1208192 128 c1208192)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1208320 128 c1208320) (checkChunk_sound 1208448 128 c1208448)) (Checked.append (checkChunk_sound 1208576 128 c1208576) (checkChunk_sound 1208704 128 c1208704))) (Checked.append (Checked.append (checkChunk_sound 1208832 128 c1208832) (checkChunk_sound 1208960 128 c1208960)) (Checked.append (checkChunk_sound 1209088 128 c1209088) (checkChunk_sound 1209216 128 c1209216)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1209344 128 c1209344) (checkChunk_sound 1209472 128 c1209472)) (Checked.append (checkChunk_sound 1209600 128 c1209600) (checkChunk_sound 1209728 128 c1209728))) (Checked.append (Checked.append (checkChunk_sound 1209856 128 c1209856) (checkChunk_sound 1209984 128 c1209984)) (Checked.append (checkChunk_sound 1210112 128 c1210112) (checkChunk_sound 1210240 128 c1210240))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1210368 128 c1210368) (checkChunk_sound 1210496 128 c1210496)) (Checked.append (checkChunk_sound 1210624 128 c1210624) (checkChunk_sound 1210752 128 c1210752))) (Checked.append (Checked.append (checkChunk_sound 1210880 128 c1210880) (checkChunk_sound 1211008 128 c1211008)) (Checked.append (checkChunk_sound 1211136 128 c1211136) (checkChunk_sound 1211264 128 c1211264)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1211392 128 c1211392) (checkChunk_sound 1211520 128 c1211520)) (Checked.append (checkChunk_sound 1211648 128 c1211648) (checkChunk_sound 1211776 128 c1211776))) (Checked.append (Checked.append (checkChunk_sound 1211904 128 c1211904) (checkChunk_sound 1212032 128 c1212032)) (Checked.append (checkChunk_sound 1212160 128 c1212160) (checkChunk_sound 1212288 128 c1212288)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B016
