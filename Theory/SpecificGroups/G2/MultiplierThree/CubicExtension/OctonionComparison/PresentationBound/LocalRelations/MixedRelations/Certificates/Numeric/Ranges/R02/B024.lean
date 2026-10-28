module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [630784, 638976).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B024
private theorem c630784 : checkChunk 630784 128 = true := by decide +kernel
private theorem c630912 : checkChunk 630912 128 = true := by decide +kernel
private theorem c631040 : checkChunk 631040 128 = true := by decide +kernel
private theorem c631168 : checkChunk 631168 128 = true := by decide +kernel
private theorem c631296 : checkChunk 631296 128 = true := by decide +kernel
private theorem c631424 : checkChunk 631424 128 = true := by decide +kernel
private theorem c631552 : checkChunk 631552 128 = true := by decide +kernel
private theorem c631680 : checkChunk 631680 128 = true := by decide +kernel
private theorem c631808 : checkChunk 631808 128 = true := by decide +kernel
private theorem c631936 : checkChunk 631936 128 = true := by decide +kernel
private theorem c632064 : checkChunk 632064 128 = true := by decide +kernel
private theorem c632192 : checkChunk 632192 128 = true := by decide +kernel
private theorem c632320 : checkChunk 632320 128 = true := by decide +kernel
private theorem c632448 : checkChunk 632448 128 = true := by decide +kernel
private theorem c632576 : checkChunk 632576 128 = true := by decide +kernel
private theorem c632704 : checkChunk 632704 128 = true := by decide +kernel
private theorem c632832 : checkChunk 632832 128 = true := by decide +kernel
private theorem c632960 : checkChunk 632960 128 = true := by decide +kernel
private theorem c633088 : checkChunk 633088 128 = true := by decide +kernel
private theorem c633216 : checkChunk 633216 128 = true := by decide +kernel
private theorem c633344 : checkChunk 633344 128 = true := by decide +kernel
private theorem c633472 : checkChunk 633472 128 = true := by decide +kernel
private theorem c633600 : checkChunk 633600 128 = true := by decide +kernel
private theorem c633728 : checkChunk 633728 128 = true := by decide +kernel
private theorem c633856 : checkChunk 633856 128 = true := by decide +kernel
private theorem c633984 : checkChunk 633984 128 = true := by decide +kernel
private theorem c634112 : checkChunk 634112 128 = true := by decide +kernel
private theorem c634240 : checkChunk 634240 128 = true := by decide +kernel
private theorem c634368 : checkChunk 634368 128 = true := by decide +kernel
private theorem c634496 : checkChunk 634496 128 = true := by decide +kernel
private theorem c634624 : checkChunk 634624 128 = true := by decide +kernel
private theorem c634752 : checkChunk 634752 128 = true := by decide +kernel
private theorem c634880 : checkChunk 634880 128 = true := by decide +kernel
private theorem c635008 : checkChunk 635008 128 = true := by decide +kernel
private theorem c635136 : checkChunk 635136 128 = true := by decide +kernel
private theorem c635264 : checkChunk 635264 128 = true := by decide +kernel
private theorem c635392 : checkChunk 635392 128 = true := by decide +kernel
private theorem c635520 : checkChunk 635520 128 = true := by decide +kernel
private theorem c635648 : checkChunk 635648 128 = true := by decide +kernel
private theorem c635776 : checkChunk 635776 128 = true := by decide +kernel
private theorem c635904 : checkChunk 635904 128 = true := by decide +kernel
private theorem c636032 : checkChunk 636032 128 = true := by decide +kernel
private theorem c636160 : checkChunk 636160 128 = true := by decide +kernel
private theorem c636288 : checkChunk 636288 128 = true := by decide +kernel
private theorem c636416 : checkChunk 636416 128 = true := by decide +kernel
private theorem c636544 : checkChunk 636544 128 = true := by decide +kernel
private theorem c636672 : checkChunk 636672 128 = true := by decide +kernel
private theorem c636800 : checkChunk 636800 128 = true := by decide +kernel
private theorem c636928 : checkChunk 636928 128 = true := by decide +kernel
private theorem c637056 : checkChunk 637056 128 = true := by decide +kernel
private theorem c637184 : checkChunk 637184 128 = true := by decide +kernel
private theorem c637312 : checkChunk 637312 128 = true := by decide +kernel
private theorem c637440 : checkChunk 637440 128 = true := by decide +kernel
private theorem c637568 : checkChunk 637568 128 = true := by decide +kernel
private theorem c637696 : checkChunk 637696 128 = true := by decide +kernel
private theorem c637824 : checkChunk 637824 128 = true := by decide +kernel
private theorem c637952 : checkChunk 637952 128 = true := by decide +kernel
private theorem c638080 : checkChunk 638080 128 = true := by decide +kernel
private theorem c638208 : checkChunk 638208 128 = true := by decide +kernel
private theorem c638336 : checkChunk 638336 128 = true := by decide +kernel
private theorem c638464 : checkChunk 638464 128 = true := by decide +kernel
private theorem c638592 : checkChunk 638592 128 = true := by decide +kernel
private theorem c638720 : checkChunk 638720 128 = true := by decide +kernel
private theorem c638848 : checkChunk 638848 128 = true := by decide +kernel

public theorem checked : Checked 630784 638976 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 630784 128 c630784) (checkChunk_sound 630912 128 c630912)) (Checked.append (checkChunk_sound 631040 128 c631040) (checkChunk_sound 631168 128 c631168))) (Checked.append (Checked.append (checkChunk_sound 631296 128 c631296) (checkChunk_sound 631424 128 c631424)) (Checked.append (checkChunk_sound 631552 128 c631552) (checkChunk_sound 631680 128 c631680)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 631808 128 c631808) (checkChunk_sound 631936 128 c631936)) (Checked.append (checkChunk_sound 632064 128 c632064) (checkChunk_sound 632192 128 c632192))) (Checked.append (Checked.append (checkChunk_sound 632320 128 c632320) (checkChunk_sound 632448 128 c632448)) (Checked.append (checkChunk_sound 632576 128 c632576) (checkChunk_sound 632704 128 c632704))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 632832 128 c632832) (checkChunk_sound 632960 128 c632960)) (Checked.append (checkChunk_sound 633088 128 c633088) (checkChunk_sound 633216 128 c633216))) (Checked.append (Checked.append (checkChunk_sound 633344 128 c633344) (checkChunk_sound 633472 128 c633472)) (Checked.append (checkChunk_sound 633600 128 c633600) (checkChunk_sound 633728 128 c633728)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 633856 128 c633856) (checkChunk_sound 633984 128 c633984)) (Checked.append (checkChunk_sound 634112 128 c634112) (checkChunk_sound 634240 128 c634240))) (Checked.append (Checked.append (checkChunk_sound 634368 128 c634368) (checkChunk_sound 634496 128 c634496)) (Checked.append (checkChunk_sound 634624 128 c634624) (checkChunk_sound 634752 128 c634752)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 634880 128 c634880) (checkChunk_sound 635008 128 c635008)) (Checked.append (checkChunk_sound 635136 128 c635136) (checkChunk_sound 635264 128 c635264))) (Checked.append (Checked.append (checkChunk_sound 635392 128 c635392) (checkChunk_sound 635520 128 c635520)) (Checked.append (checkChunk_sound 635648 128 c635648) (checkChunk_sound 635776 128 c635776)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 635904 128 c635904) (checkChunk_sound 636032 128 c636032)) (Checked.append (checkChunk_sound 636160 128 c636160) (checkChunk_sound 636288 128 c636288))) (Checked.append (Checked.append (checkChunk_sound 636416 128 c636416) (checkChunk_sound 636544 128 c636544)) (Checked.append (checkChunk_sound 636672 128 c636672) (checkChunk_sound 636800 128 c636800))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 636928 128 c636928) (checkChunk_sound 637056 128 c637056)) (Checked.append (checkChunk_sound 637184 128 c637184) (checkChunk_sound 637312 128 c637312))) (Checked.append (Checked.append (checkChunk_sound 637440 128 c637440) (checkChunk_sound 637568 128 c637568)) (Checked.append (checkChunk_sound 637696 128 c637696) (checkChunk_sound 637824 128 c637824)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 637952 128 c637952) (checkChunk_sound 638080 128 c638080)) (Checked.append (checkChunk_sound 638208 128 c638208) (checkChunk_sound 638336 128 c638336))) (Checked.append (Checked.append (checkChunk_sound 638464 128 c638464) (checkChunk_sound 638592 128 c638592)) (Checked.append (checkChunk_sound 638720 128 c638720) (checkChunk_sound 638848 128 c638848)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B024
