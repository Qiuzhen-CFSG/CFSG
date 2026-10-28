module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [581632, 589824).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B018
private theorem c581632 : checkChunk 581632 128 = true := by decide +kernel
private theorem c581760 : checkChunk 581760 128 = true := by decide +kernel
private theorem c581888 : checkChunk 581888 128 = true := by decide +kernel
private theorem c582016 : checkChunk 582016 128 = true := by decide +kernel
private theorem c582144 : checkChunk 582144 128 = true := by decide +kernel
private theorem c582272 : checkChunk 582272 128 = true := by decide +kernel
private theorem c582400 : checkChunk 582400 128 = true := by decide +kernel
private theorem c582528 : checkChunk 582528 128 = true := by decide +kernel
private theorem c582656 : checkChunk 582656 128 = true := by decide +kernel
private theorem c582784 : checkChunk 582784 128 = true := by decide +kernel
private theorem c582912 : checkChunk 582912 128 = true := by decide +kernel
private theorem c583040 : checkChunk 583040 128 = true := by decide +kernel
private theorem c583168 : checkChunk 583168 128 = true := by decide +kernel
private theorem c583296 : checkChunk 583296 128 = true := by decide +kernel
private theorem c583424 : checkChunk 583424 128 = true := by decide +kernel
private theorem c583552 : checkChunk 583552 128 = true := by decide +kernel
private theorem c583680 : checkChunk 583680 128 = true := by decide +kernel
private theorem c583808 : checkChunk 583808 128 = true := by decide +kernel
private theorem c583936 : checkChunk 583936 128 = true := by decide +kernel
private theorem c584064 : checkChunk 584064 128 = true := by decide +kernel
private theorem c584192 : checkChunk 584192 128 = true := by decide +kernel
private theorem c584320 : checkChunk 584320 128 = true := by decide +kernel
private theorem c584448 : checkChunk 584448 128 = true := by decide +kernel
private theorem c584576 : checkChunk 584576 128 = true := by decide +kernel
private theorem c584704 : checkChunk 584704 128 = true := by decide +kernel
private theorem c584832 : checkChunk 584832 128 = true := by decide +kernel
private theorem c584960 : checkChunk 584960 128 = true := by decide +kernel
private theorem c585088 : checkChunk 585088 128 = true := by decide +kernel
private theorem c585216 : checkChunk 585216 128 = true := by decide +kernel
private theorem c585344 : checkChunk 585344 128 = true := by decide +kernel
private theorem c585472 : checkChunk 585472 128 = true := by decide +kernel
private theorem c585600 : checkChunk 585600 128 = true := by decide +kernel
private theorem c585728 : checkChunk 585728 128 = true := by decide +kernel
private theorem c585856 : checkChunk 585856 128 = true := by decide +kernel
private theorem c585984 : checkChunk 585984 128 = true := by decide +kernel
private theorem c586112 : checkChunk 586112 128 = true := by decide +kernel
private theorem c586240 : checkChunk 586240 128 = true := by decide +kernel
private theorem c586368 : checkChunk 586368 128 = true := by decide +kernel
private theorem c586496 : checkChunk 586496 128 = true := by decide +kernel
private theorem c586624 : checkChunk 586624 128 = true := by decide +kernel
private theorem c586752 : checkChunk 586752 128 = true := by decide +kernel
private theorem c586880 : checkChunk 586880 128 = true := by decide +kernel
private theorem c587008 : checkChunk 587008 128 = true := by decide +kernel
private theorem c587136 : checkChunk 587136 128 = true := by decide +kernel
private theorem c587264 : checkChunk 587264 128 = true := by decide +kernel
private theorem c587392 : checkChunk 587392 128 = true := by decide +kernel
private theorem c587520 : checkChunk 587520 128 = true := by decide +kernel
private theorem c587648 : checkChunk 587648 128 = true := by decide +kernel
private theorem c587776 : checkChunk 587776 128 = true := by decide +kernel
private theorem c587904 : checkChunk 587904 128 = true := by decide +kernel
private theorem c588032 : checkChunk 588032 128 = true := by decide +kernel
private theorem c588160 : checkChunk 588160 128 = true := by decide +kernel
private theorem c588288 : checkChunk 588288 128 = true := by decide +kernel
private theorem c588416 : checkChunk 588416 128 = true := by decide +kernel
private theorem c588544 : checkChunk 588544 128 = true := by decide +kernel
private theorem c588672 : checkChunk 588672 128 = true := by decide +kernel
private theorem c588800 : checkChunk 588800 128 = true := by decide +kernel
private theorem c588928 : checkChunk 588928 128 = true := by decide +kernel
private theorem c589056 : checkChunk 589056 128 = true := by decide +kernel
private theorem c589184 : checkChunk 589184 128 = true := by decide +kernel
private theorem c589312 : checkChunk 589312 128 = true := by decide +kernel
private theorem c589440 : checkChunk 589440 128 = true := by decide +kernel
private theorem c589568 : checkChunk 589568 128 = true := by decide +kernel
private theorem c589696 : checkChunk 589696 128 = true := by decide +kernel

public theorem checked : Checked 581632 589824 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 581632 128 c581632) (checkChunk_sound 581760 128 c581760)) (Checked.append (checkChunk_sound 581888 128 c581888) (checkChunk_sound 582016 128 c582016))) (Checked.append (Checked.append (checkChunk_sound 582144 128 c582144) (checkChunk_sound 582272 128 c582272)) (Checked.append (checkChunk_sound 582400 128 c582400) (checkChunk_sound 582528 128 c582528)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 582656 128 c582656) (checkChunk_sound 582784 128 c582784)) (Checked.append (checkChunk_sound 582912 128 c582912) (checkChunk_sound 583040 128 c583040))) (Checked.append (Checked.append (checkChunk_sound 583168 128 c583168) (checkChunk_sound 583296 128 c583296)) (Checked.append (checkChunk_sound 583424 128 c583424) (checkChunk_sound 583552 128 c583552))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 583680 128 c583680) (checkChunk_sound 583808 128 c583808)) (Checked.append (checkChunk_sound 583936 128 c583936) (checkChunk_sound 584064 128 c584064))) (Checked.append (Checked.append (checkChunk_sound 584192 128 c584192) (checkChunk_sound 584320 128 c584320)) (Checked.append (checkChunk_sound 584448 128 c584448) (checkChunk_sound 584576 128 c584576)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 584704 128 c584704) (checkChunk_sound 584832 128 c584832)) (Checked.append (checkChunk_sound 584960 128 c584960) (checkChunk_sound 585088 128 c585088))) (Checked.append (Checked.append (checkChunk_sound 585216 128 c585216) (checkChunk_sound 585344 128 c585344)) (Checked.append (checkChunk_sound 585472 128 c585472) (checkChunk_sound 585600 128 c585600)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 585728 128 c585728) (checkChunk_sound 585856 128 c585856)) (Checked.append (checkChunk_sound 585984 128 c585984) (checkChunk_sound 586112 128 c586112))) (Checked.append (Checked.append (checkChunk_sound 586240 128 c586240) (checkChunk_sound 586368 128 c586368)) (Checked.append (checkChunk_sound 586496 128 c586496) (checkChunk_sound 586624 128 c586624)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 586752 128 c586752) (checkChunk_sound 586880 128 c586880)) (Checked.append (checkChunk_sound 587008 128 c587008) (checkChunk_sound 587136 128 c587136))) (Checked.append (Checked.append (checkChunk_sound 587264 128 c587264) (checkChunk_sound 587392 128 c587392)) (Checked.append (checkChunk_sound 587520 128 c587520) (checkChunk_sound 587648 128 c587648))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 587776 128 c587776) (checkChunk_sound 587904 128 c587904)) (Checked.append (checkChunk_sound 588032 128 c588032) (checkChunk_sound 588160 128 c588160))) (Checked.append (Checked.append (checkChunk_sound 588288 128 c588288) (checkChunk_sound 588416 128 c588416)) (Checked.append (checkChunk_sound 588544 128 c588544) (checkChunk_sound 588672 128 c588672)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 588800 128 c588800) (checkChunk_sound 588928 128 c588928)) (Checked.append (checkChunk_sound 589056 128 c589056) (checkChunk_sound 589184 128 c589184))) (Checked.append (Checked.append (checkChunk_sound 589312 128 c589312) (checkChunk_sound 589440 128 c589440)) (Checked.append (checkChunk_sound 589568 128 c589568) (checkChunk_sound 589696 128 c589696)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B018
