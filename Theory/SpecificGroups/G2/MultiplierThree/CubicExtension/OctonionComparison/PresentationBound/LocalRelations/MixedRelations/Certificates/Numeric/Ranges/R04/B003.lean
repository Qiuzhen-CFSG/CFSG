module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [884736, 892928).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B003
private theorem c884736 : checkChunk 884736 128 = true := by decide +kernel
private theorem c884864 : checkChunk 884864 128 = true := by decide +kernel
private theorem c884992 : checkChunk 884992 128 = true := by decide +kernel
private theorem c885120 : checkChunk 885120 128 = true := by decide +kernel
private theorem c885248 : checkChunk 885248 128 = true := by decide +kernel
private theorem c885376 : checkChunk 885376 128 = true := by decide +kernel
private theorem c885504 : checkChunk 885504 128 = true := by decide +kernel
private theorem c885632 : checkChunk 885632 128 = true := by decide +kernel
private theorem c885760 : checkChunk 885760 128 = true := by decide +kernel
private theorem c885888 : checkChunk 885888 128 = true := by decide +kernel
private theorem c886016 : checkChunk 886016 128 = true := by decide +kernel
private theorem c886144 : checkChunk 886144 128 = true := by decide +kernel
private theorem c886272 : checkChunk 886272 128 = true := by decide +kernel
private theorem c886400 : checkChunk 886400 128 = true := by decide +kernel
private theorem c886528 : checkChunk 886528 128 = true := by decide +kernel
private theorem c886656 : checkChunk 886656 128 = true := by decide +kernel
private theorem c886784 : checkChunk 886784 128 = true := by decide +kernel
private theorem c886912 : checkChunk 886912 128 = true := by decide +kernel
private theorem c887040 : checkChunk 887040 128 = true := by decide +kernel
private theorem c887168 : checkChunk 887168 128 = true := by decide +kernel
private theorem c887296 : checkChunk 887296 128 = true := by decide +kernel
private theorem c887424 : checkChunk 887424 128 = true := by decide +kernel
private theorem c887552 : checkChunk 887552 128 = true := by decide +kernel
private theorem c887680 : checkChunk 887680 128 = true := by decide +kernel
private theorem c887808 : checkChunk 887808 128 = true := by decide +kernel
private theorem c887936 : checkChunk 887936 128 = true := by decide +kernel
private theorem c888064 : checkChunk 888064 128 = true := by decide +kernel
private theorem c888192 : checkChunk 888192 128 = true := by decide +kernel
private theorem c888320 : checkChunk 888320 128 = true := by decide +kernel
private theorem c888448 : checkChunk 888448 128 = true := by decide +kernel
private theorem c888576 : checkChunk 888576 128 = true := by decide +kernel
private theorem c888704 : checkChunk 888704 128 = true := by decide +kernel
private theorem c888832 : checkChunk 888832 128 = true := by decide +kernel
private theorem c888960 : checkChunk 888960 128 = true := by decide +kernel
private theorem c889088 : checkChunk 889088 128 = true := by decide +kernel
private theorem c889216 : checkChunk 889216 128 = true := by decide +kernel
private theorem c889344 : checkChunk 889344 128 = true := by decide +kernel
private theorem c889472 : checkChunk 889472 128 = true := by decide +kernel
private theorem c889600 : checkChunk 889600 128 = true := by decide +kernel
private theorem c889728 : checkChunk 889728 128 = true := by decide +kernel
private theorem c889856 : checkChunk 889856 128 = true := by decide +kernel
private theorem c889984 : checkChunk 889984 128 = true := by decide +kernel
private theorem c890112 : checkChunk 890112 128 = true := by decide +kernel
private theorem c890240 : checkChunk 890240 128 = true := by decide +kernel
private theorem c890368 : checkChunk 890368 128 = true := by decide +kernel
private theorem c890496 : checkChunk 890496 128 = true := by decide +kernel
private theorem c890624 : checkChunk 890624 128 = true := by decide +kernel
private theorem c890752 : checkChunk 890752 128 = true := by decide +kernel
private theorem c890880 : checkChunk 890880 128 = true := by decide +kernel
private theorem c891008 : checkChunk 891008 128 = true := by decide +kernel
private theorem c891136 : checkChunk 891136 128 = true := by decide +kernel
private theorem c891264 : checkChunk 891264 128 = true := by decide +kernel
private theorem c891392 : checkChunk 891392 128 = true := by decide +kernel
private theorem c891520 : checkChunk 891520 128 = true := by decide +kernel
private theorem c891648 : checkChunk 891648 128 = true := by decide +kernel
private theorem c891776 : checkChunk 891776 128 = true := by decide +kernel
private theorem c891904 : checkChunk 891904 128 = true := by decide +kernel
private theorem c892032 : checkChunk 892032 128 = true := by decide +kernel
private theorem c892160 : checkChunk 892160 128 = true := by decide +kernel
private theorem c892288 : checkChunk 892288 128 = true := by decide +kernel
private theorem c892416 : checkChunk 892416 128 = true := by decide +kernel
private theorem c892544 : checkChunk 892544 128 = true := by decide +kernel
private theorem c892672 : checkChunk 892672 128 = true := by decide +kernel
private theorem c892800 : checkChunk 892800 128 = true := by decide +kernel

public theorem checked : Checked 884736 892928 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 884736 128 c884736) (checkChunk_sound 884864 128 c884864)) (Checked.append (checkChunk_sound 884992 128 c884992) (checkChunk_sound 885120 128 c885120))) (Checked.append (Checked.append (checkChunk_sound 885248 128 c885248) (checkChunk_sound 885376 128 c885376)) (Checked.append (checkChunk_sound 885504 128 c885504) (checkChunk_sound 885632 128 c885632)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 885760 128 c885760) (checkChunk_sound 885888 128 c885888)) (Checked.append (checkChunk_sound 886016 128 c886016) (checkChunk_sound 886144 128 c886144))) (Checked.append (Checked.append (checkChunk_sound 886272 128 c886272) (checkChunk_sound 886400 128 c886400)) (Checked.append (checkChunk_sound 886528 128 c886528) (checkChunk_sound 886656 128 c886656))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 886784 128 c886784) (checkChunk_sound 886912 128 c886912)) (Checked.append (checkChunk_sound 887040 128 c887040) (checkChunk_sound 887168 128 c887168))) (Checked.append (Checked.append (checkChunk_sound 887296 128 c887296) (checkChunk_sound 887424 128 c887424)) (Checked.append (checkChunk_sound 887552 128 c887552) (checkChunk_sound 887680 128 c887680)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 887808 128 c887808) (checkChunk_sound 887936 128 c887936)) (Checked.append (checkChunk_sound 888064 128 c888064) (checkChunk_sound 888192 128 c888192))) (Checked.append (Checked.append (checkChunk_sound 888320 128 c888320) (checkChunk_sound 888448 128 c888448)) (Checked.append (checkChunk_sound 888576 128 c888576) (checkChunk_sound 888704 128 c888704)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 888832 128 c888832) (checkChunk_sound 888960 128 c888960)) (Checked.append (checkChunk_sound 889088 128 c889088) (checkChunk_sound 889216 128 c889216))) (Checked.append (Checked.append (checkChunk_sound 889344 128 c889344) (checkChunk_sound 889472 128 c889472)) (Checked.append (checkChunk_sound 889600 128 c889600) (checkChunk_sound 889728 128 c889728)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 889856 128 c889856) (checkChunk_sound 889984 128 c889984)) (Checked.append (checkChunk_sound 890112 128 c890112) (checkChunk_sound 890240 128 c890240))) (Checked.append (Checked.append (checkChunk_sound 890368 128 c890368) (checkChunk_sound 890496 128 c890496)) (Checked.append (checkChunk_sound 890624 128 c890624) (checkChunk_sound 890752 128 c890752))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 890880 128 c890880) (checkChunk_sound 891008 128 c891008)) (Checked.append (checkChunk_sound 891136 128 c891136) (checkChunk_sound 891264 128 c891264))) (Checked.append (Checked.append (checkChunk_sound 891392 128 c891392) (checkChunk_sound 891520 128 c891520)) (Checked.append (checkChunk_sound 891648 128 c891648) (checkChunk_sound 891776 128 c891776)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 891904 128 c891904) (checkChunk_sound 892032 128 c892032)) (Checked.append (checkChunk_sound 892160 128 c892160) (checkChunk_sound 892288 128 c892288))) (Checked.append (Checked.append (checkChunk_sound 892416 128 c892416) (checkChunk_sound 892544 128 c892544)) (Checked.append (checkChunk_sound 892672 128 c892672) (checkChunk_sound 892800 128 c892800)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B003
