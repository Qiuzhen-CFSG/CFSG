module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [180224, 188416).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B021
private theorem c180224 : checkChunk 180224 128 = true := by decide +kernel
private theorem c180352 : checkChunk 180352 128 = true := by decide +kernel
private theorem c180480 : checkChunk 180480 128 = true := by decide +kernel
private theorem c180608 : checkChunk 180608 128 = true := by decide +kernel
private theorem c180736 : checkChunk 180736 128 = true := by decide +kernel
private theorem c180864 : checkChunk 180864 128 = true := by decide +kernel
private theorem c180992 : checkChunk 180992 128 = true := by decide +kernel
private theorem c181120 : checkChunk 181120 128 = true := by decide +kernel
private theorem c181248 : checkChunk 181248 128 = true := by decide +kernel
private theorem c181376 : checkChunk 181376 128 = true := by decide +kernel
private theorem c181504 : checkChunk 181504 128 = true := by decide +kernel
private theorem c181632 : checkChunk 181632 128 = true := by decide +kernel
private theorem c181760 : checkChunk 181760 128 = true := by decide +kernel
private theorem c181888 : checkChunk 181888 128 = true := by decide +kernel
private theorem c182016 : checkChunk 182016 128 = true := by decide +kernel
private theorem c182144 : checkChunk 182144 128 = true := by decide +kernel
private theorem c182272 : checkChunk 182272 128 = true := by decide +kernel
private theorem c182400 : checkChunk 182400 128 = true := by decide +kernel
private theorem c182528 : checkChunk 182528 128 = true := by decide +kernel
private theorem c182656 : checkChunk 182656 128 = true := by decide +kernel
private theorem c182784 : checkChunk 182784 128 = true := by decide +kernel
private theorem c182912 : checkChunk 182912 128 = true := by decide +kernel
private theorem c183040 : checkChunk 183040 128 = true := by decide +kernel
private theorem c183168 : checkChunk 183168 128 = true := by decide +kernel
private theorem c183296 : checkChunk 183296 128 = true := by decide +kernel
private theorem c183424 : checkChunk 183424 128 = true := by decide +kernel
private theorem c183552 : checkChunk 183552 128 = true := by decide +kernel
private theorem c183680 : checkChunk 183680 128 = true := by decide +kernel
private theorem c183808 : checkChunk 183808 128 = true := by decide +kernel
private theorem c183936 : checkChunk 183936 128 = true := by decide +kernel
private theorem c184064 : checkChunk 184064 128 = true := by decide +kernel
private theorem c184192 : checkChunk 184192 128 = true := by decide +kernel
private theorem c184320 : checkChunk 184320 128 = true := by decide +kernel
private theorem c184448 : checkChunk 184448 128 = true := by decide +kernel
private theorem c184576 : checkChunk 184576 128 = true := by decide +kernel
private theorem c184704 : checkChunk 184704 128 = true := by decide +kernel
private theorem c184832 : checkChunk 184832 128 = true := by decide +kernel
private theorem c184960 : checkChunk 184960 128 = true := by decide +kernel
private theorem c185088 : checkChunk 185088 128 = true := by decide +kernel
private theorem c185216 : checkChunk 185216 128 = true := by decide +kernel
private theorem c185344 : checkChunk 185344 128 = true := by decide +kernel
private theorem c185472 : checkChunk 185472 128 = true := by decide +kernel
private theorem c185600 : checkChunk 185600 128 = true := by decide +kernel
private theorem c185728 : checkChunk 185728 128 = true := by decide +kernel
private theorem c185856 : checkChunk 185856 128 = true := by decide +kernel
private theorem c185984 : checkChunk 185984 128 = true := by decide +kernel
private theorem c186112 : checkChunk 186112 128 = true := by decide +kernel
private theorem c186240 : checkChunk 186240 128 = true := by decide +kernel
private theorem c186368 : checkChunk 186368 128 = true := by decide +kernel
private theorem c186496 : checkChunk 186496 128 = true := by decide +kernel
private theorem c186624 : checkChunk 186624 128 = true := by decide +kernel
private theorem c186752 : checkChunk 186752 128 = true := by decide +kernel
private theorem c186880 : checkChunk 186880 128 = true := by decide +kernel
private theorem c187008 : checkChunk 187008 128 = true := by decide +kernel
private theorem c187136 : checkChunk 187136 128 = true := by decide +kernel
private theorem c187264 : checkChunk 187264 128 = true := by decide +kernel
private theorem c187392 : checkChunk 187392 128 = true := by decide +kernel
private theorem c187520 : checkChunk 187520 128 = true := by decide +kernel
private theorem c187648 : checkChunk 187648 128 = true := by decide +kernel
private theorem c187776 : checkChunk 187776 128 = true := by decide +kernel
private theorem c187904 : checkChunk 187904 128 = true := by decide +kernel
private theorem c188032 : checkChunk 188032 128 = true := by decide +kernel
private theorem c188160 : checkChunk 188160 128 = true := by decide +kernel
private theorem c188288 : checkChunk 188288 128 = true := by decide +kernel

public theorem checked : Checked 180224 188416 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 180224 128 c180224) (checkChunk_sound 180352 128 c180352)) (Checked.append (checkChunk_sound 180480 128 c180480) (checkChunk_sound 180608 128 c180608))) (Checked.append (Checked.append (checkChunk_sound 180736 128 c180736) (checkChunk_sound 180864 128 c180864)) (Checked.append (checkChunk_sound 180992 128 c180992) (checkChunk_sound 181120 128 c181120)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 181248 128 c181248) (checkChunk_sound 181376 128 c181376)) (Checked.append (checkChunk_sound 181504 128 c181504) (checkChunk_sound 181632 128 c181632))) (Checked.append (Checked.append (checkChunk_sound 181760 128 c181760) (checkChunk_sound 181888 128 c181888)) (Checked.append (checkChunk_sound 182016 128 c182016) (checkChunk_sound 182144 128 c182144))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 182272 128 c182272) (checkChunk_sound 182400 128 c182400)) (Checked.append (checkChunk_sound 182528 128 c182528) (checkChunk_sound 182656 128 c182656))) (Checked.append (Checked.append (checkChunk_sound 182784 128 c182784) (checkChunk_sound 182912 128 c182912)) (Checked.append (checkChunk_sound 183040 128 c183040) (checkChunk_sound 183168 128 c183168)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 183296 128 c183296) (checkChunk_sound 183424 128 c183424)) (Checked.append (checkChunk_sound 183552 128 c183552) (checkChunk_sound 183680 128 c183680))) (Checked.append (Checked.append (checkChunk_sound 183808 128 c183808) (checkChunk_sound 183936 128 c183936)) (Checked.append (checkChunk_sound 184064 128 c184064) (checkChunk_sound 184192 128 c184192)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 184320 128 c184320) (checkChunk_sound 184448 128 c184448)) (Checked.append (checkChunk_sound 184576 128 c184576) (checkChunk_sound 184704 128 c184704))) (Checked.append (Checked.append (checkChunk_sound 184832 128 c184832) (checkChunk_sound 184960 128 c184960)) (Checked.append (checkChunk_sound 185088 128 c185088) (checkChunk_sound 185216 128 c185216)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 185344 128 c185344) (checkChunk_sound 185472 128 c185472)) (Checked.append (checkChunk_sound 185600 128 c185600) (checkChunk_sound 185728 128 c185728))) (Checked.append (Checked.append (checkChunk_sound 185856 128 c185856) (checkChunk_sound 185984 128 c185984)) (Checked.append (checkChunk_sound 186112 128 c186112) (checkChunk_sound 186240 128 c186240))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 186368 128 c186368) (checkChunk_sound 186496 128 c186496)) (Checked.append (checkChunk_sound 186624 128 c186624) (checkChunk_sound 186752 128 c186752))) (Checked.append (Checked.append (checkChunk_sound 186880 128 c186880) (checkChunk_sound 187008 128 c187008)) (Checked.append (checkChunk_sound 187136 128 c187136) (checkChunk_sound 187264 128 c187264)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 187392 128 c187392) (checkChunk_sound 187520 128 c187520)) (Checked.append (checkChunk_sound 187648 128 c187648) (checkChunk_sound 187776 128 c187776))) (Checked.append (Checked.append (checkChunk_sound 187904 128 c187904) (checkChunk_sound 188032 128 c188032)) (Checked.append (checkChunk_sound 188160 128 c188160) (checkChunk_sound 188288 128 c188288)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B021
