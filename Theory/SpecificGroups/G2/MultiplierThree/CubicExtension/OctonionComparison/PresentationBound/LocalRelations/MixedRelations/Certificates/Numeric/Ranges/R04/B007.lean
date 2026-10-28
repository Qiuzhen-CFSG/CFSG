module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [917504, 925696).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B007
private theorem c917504 : checkChunk 917504 128 = true := by decide +kernel
private theorem c917632 : checkChunk 917632 128 = true := by decide +kernel
private theorem c917760 : checkChunk 917760 128 = true := by decide +kernel
private theorem c917888 : checkChunk 917888 128 = true := by decide +kernel
private theorem c918016 : checkChunk 918016 128 = true := by decide +kernel
private theorem c918144 : checkChunk 918144 128 = true := by decide +kernel
private theorem c918272 : checkChunk 918272 128 = true := by decide +kernel
private theorem c918400 : checkChunk 918400 128 = true := by decide +kernel
private theorem c918528 : checkChunk 918528 128 = true := by decide +kernel
private theorem c918656 : checkChunk 918656 128 = true := by decide +kernel
private theorem c918784 : checkChunk 918784 128 = true := by decide +kernel
private theorem c918912 : checkChunk 918912 128 = true := by decide +kernel
private theorem c919040 : checkChunk 919040 128 = true := by decide +kernel
private theorem c919168 : checkChunk 919168 128 = true := by decide +kernel
private theorem c919296 : checkChunk 919296 128 = true := by decide +kernel
private theorem c919424 : checkChunk 919424 128 = true := by decide +kernel
private theorem c919552 : checkChunk 919552 128 = true := by decide +kernel
private theorem c919680 : checkChunk 919680 128 = true := by decide +kernel
private theorem c919808 : checkChunk 919808 128 = true := by decide +kernel
private theorem c919936 : checkChunk 919936 128 = true := by decide +kernel
private theorem c920064 : checkChunk 920064 128 = true := by decide +kernel
private theorem c920192 : checkChunk 920192 128 = true := by decide +kernel
private theorem c920320 : checkChunk 920320 128 = true := by decide +kernel
private theorem c920448 : checkChunk 920448 128 = true := by decide +kernel
private theorem c920576 : checkChunk 920576 128 = true := by decide +kernel
private theorem c920704 : checkChunk 920704 128 = true := by decide +kernel
private theorem c920832 : checkChunk 920832 128 = true := by decide +kernel
private theorem c920960 : checkChunk 920960 128 = true := by decide +kernel
private theorem c921088 : checkChunk 921088 128 = true := by decide +kernel
private theorem c921216 : checkChunk 921216 128 = true := by decide +kernel
private theorem c921344 : checkChunk 921344 128 = true := by decide +kernel
private theorem c921472 : checkChunk 921472 128 = true := by decide +kernel
private theorem c921600 : checkChunk 921600 128 = true := by decide +kernel
private theorem c921728 : checkChunk 921728 128 = true := by decide +kernel
private theorem c921856 : checkChunk 921856 128 = true := by decide +kernel
private theorem c921984 : checkChunk 921984 128 = true := by decide +kernel
private theorem c922112 : checkChunk 922112 128 = true := by decide +kernel
private theorem c922240 : checkChunk 922240 128 = true := by decide +kernel
private theorem c922368 : checkChunk 922368 128 = true := by decide +kernel
private theorem c922496 : checkChunk 922496 128 = true := by decide +kernel
private theorem c922624 : checkChunk 922624 128 = true := by decide +kernel
private theorem c922752 : checkChunk 922752 128 = true := by decide +kernel
private theorem c922880 : checkChunk 922880 128 = true := by decide +kernel
private theorem c923008 : checkChunk 923008 128 = true := by decide +kernel
private theorem c923136 : checkChunk 923136 128 = true := by decide +kernel
private theorem c923264 : checkChunk 923264 128 = true := by decide +kernel
private theorem c923392 : checkChunk 923392 128 = true := by decide +kernel
private theorem c923520 : checkChunk 923520 128 = true := by decide +kernel
private theorem c923648 : checkChunk 923648 128 = true := by decide +kernel
private theorem c923776 : checkChunk 923776 128 = true := by decide +kernel
private theorem c923904 : checkChunk 923904 128 = true := by decide +kernel
private theorem c924032 : checkChunk 924032 128 = true := by decide +kernel
private theorem c924160 : checkChunk 924160 128 = true := by decide +kernel
private theorem c924288 : checkChunk 924288 128 = true := by decide +kernel
private theorem c924416 : checkChunk 924416 128 = true := by decide +kernel
private theorem c924544 : checkChunk 924544 128 = true := by decide +kernel
private theorem c924672 : checkChunk 924672 128 = true := by decide +kernel
private theorem c924800 : checkChunk 924800 128 = true := by decide +kernel
private theorem c924928 : checkChunk 924928 128 = true := by decide +kernel
private theorem c925056 : checkChunk 925056 128 = true := by decide +kernel
private theorem c925184 : checkChunk 925184 128 = true := by decide +kernel
private theorem c925312 : checkChunk 925312 128 = true := by decide +kernel
private theorem c925440 : checkChunk 925440 128 = true := by decide +kernel
private theorem c925568 : checkChunk 925568 128 = true := by decide +kernel

public theorem checked : Checked 917504 925696 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 917504 128 c917504) (checkChunk_sound 917632 128 c917632)) (Checked.append (checkChunk_sound 917760 128 c917760) (checkChunk_sound 917888 128 c917888))) (Checked.append (Checked.append (checkChunk_sound 918016 128 c918016) (checkChunk_sound 918144 128 c918144)) (Checked.append (checkChunk_sound 918272 128 c918272) (checkChunk_sound 918400 128 c918400)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 918528 128 c918528) (checkChunk_sound 918656 128 c918656)) (Checked.append (checkChunk_sound 918784 128 c918784) (checkChunk_sound 918912 128 c918912))) (Checked.append (Checked.append (checkChunk_sound 919040 128 c919040) (checkChunk_sound 919168 128 c919168)) (Checked.append (checkChunk_sound 919296 128 c919296) (checkChunk_sound 919424 128 c919424))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 919552 128 c919552) (checkChunk_sound 919680 128 c919680)) (Checked.append (checkChunk_sound 919808 128 c919808) (checkChunk_sound 919936 128 c919936))) (Checked.append (Checked.append (checkChunk_sound 920064 128 c920064) (checkChunk_sound 920192 128 c920192)) (Checked.append (checkChunk_sound 920320 128 c920320) (checkChunk_sound 920448 128 c920448)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 920576 128 c920576) (checkChunk_sound 920704 128 c920704)) (Checked.append (checkChunk_sound 920832 128 c920832) (checkChunk_sound 920960 128 c920960))) (Checked.append (Checked.append (checkChunk_sound 921088 128 c921088) (checkChunk_sound 921216 128 c921216)) (Checked.append (checkChunk_sound 921344 128 c921344) (checkChunk_sound 921472 128 c921472)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 921600 128 c921600) (checkChunk_sound 921728 128 c921728)) (Checked.append (checkChunk_sound 921856 128 c921856) (checkChunk_sound 921984 128 c921984))) (Checked.append (Checked.append (checkChunk_sound 922112 128 c922112) (checkChunk_sound 922240 128 c922240)) (Checked.append (checkChunk_sound 922368 128 c922368) (checkChunk_sound 922496 128 c922496)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 922624 128 c922624) (checkChunk_sound 922752 128 c922752)) (Checked.append (checkChunk_sound 922880 128 c922880) (checkChunk_sound 923008 128 c923008))) (Checked.append (Checked.append (checkChunk_sound 923136 128 c923136) (checkChunk_sound 923264 128 c923264)) (Checked.append (checkChunk_sound 923392 128 c923392) (checkChunk_sound 923520 128 c923520))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 923648 128 c923648) (checkChunk_sound 923776 128 c923776)) (Checked.append (checkChunk_sound 923904 128 c923904) (checkChunk_sound 924032 128 c924032))) (Checked.append (Checked.append (checkChunk_sound 924160 128 c924160) (checkChunk_sound 924288 128 c924288)) (Checked.append (checkChunk_sound 924416 128 c924416) (checkChunk_sound 924544 128 c924544)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 924672 128 c924672) (checkChunk_sound 924800 128 c924800)) (Checked.append (checkChunk_sound 924928 128 c924928) (checkChunk_sound 925056 128 c925056))) (Checked.append (Checked.append (checkChunk_sound 925184 128 c925184) (checkChunk_sound 925312 128 c925312)) (Checked.append (checkChunk_sound 925440 128 c925440) (checkChunk_sound 925568 128 c925568)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B007
