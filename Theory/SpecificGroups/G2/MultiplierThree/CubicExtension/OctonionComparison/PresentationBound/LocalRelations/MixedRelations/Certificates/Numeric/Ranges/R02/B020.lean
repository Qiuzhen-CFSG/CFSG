module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [598016, 606208).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B020
private theorem c598016 : checkChunk 598016 128 = true := by decide +kernel
private theorem c598144 : checkChunk 598144 128 = true := by decide +kernel
private theorem c598272 : checkChunk 598272 128 = true := by decide +kernel
private theorem c598400 : checkChunk 598400 128 = true := by decide +kernel
private theorem c598528 : checkChunk 598528 128 = true := by decide +kernel
private theorem c598656 : checkChunk 598656 128 = true := by decide +kernel
private theorem c598784 : checkChunk 598784 128 = true := by decide +kernel
private theorem c598912 : checkChunk 598912 128 = true := by decide +kernel
private theorem c599040 : checkChunk 599040 128 = true := by decide +kernel
private theorem c599168 : checkChunk 599168 128 = true := by decide +kernel
private theorem c599296 : checkChunk 599296 128 = true := by decide +kernel
private theorem c599424 : checkChunk 599424 128 = true := by decide +kernel
private theorem c599552 : checkChunk 599552 128 = true := by decide +kernel
private theorem c599680 : checkChunk 599680 128 = true := by decide +kernel
private theorem c599808 : checkChunk 599808 128 = true := by decide +kernel
private theorem c599936 : checkChunk 599936 128 = true := by decide +kernel
private theorem c600064 : checkChunk 600064 128 = true := by decide +kernel
private theorem c600192 : checkChunk 600192 128 = true := by decide +kernel
private theorem c600320 : checkChunk 600320 128 = true := by decide +kernel
private theorem c600448 : checkChunk 600448 128 = true := by decide +kernel
private theorem c600576 : checkChunk 600576 128 = true := by decide +kernel
private theorem c600704 : checkChunk 600704 128 = true := by decide +kernel
private theorem c600832 : checkChunk 600832 128 = true := by decide +kernel
private theorem c600960 : checkChunk 600960 128 = true := by decide +kernel
private theorem c601088 : checkChunk 601088 128 = true := by decide +kernel
private theorem c601216 : checkChunk 601216 128 = true := by decide +kernel
private theorem c601344 : checkChunk 601344 128 = true := by decide +kernel
private theorem c601472 : checkChunk 601472 128 = true := by decide +kernel
private theorem c601600 : checkChunk 601600 128 = true := by decide +kernel
private theorem c601728 : checkChunk 601728 128 = true := by decide +kernel
private theorem c601856 : checkChunk 601856 128 = true := by decide +kernel
private theorem c601984 : checkChunk 601984 128 = true := by decide +kernel
private theorem c602112 : checkChunk 602112 128 = true := by decide +kernel
private theorem c602240 : checkChunk 602240 128 = true := by decide +kernel
private theorem c602368 : checkChunk 602368 128 = true := by decide +kernel
private theorem c602496 : checkChunk 602496 128 = true := by decide +kernel
private theorem c602624 : checkChunk 602624 128 = true := by decide +kernel
private theorem c602752 : checkChunk 602752 128 = true := by decide +kernel
private theorem c602880 : checkChunk 602880 128 = true := by decide +kernel
private theorem c603008 : checkChunk 603008 128 = true := by decide +kernel
private theorem c603136 : checkChunk 603136 128 = true := by decide +kernel
private theorem c603264 : checkChunk 603264 128 = true := by decide +kernel
private theorem c603392 : checkChunk 603392 128 = true := by decide +kernel
private theorem c603520 : checkChunk 603520 128 = true := by decide +kernel
private theorem c603648 : checkChunk 603648 128 = true := by decide +kernel
private theorem c603776 : checkChunk 603776 128 = true := by decide +kernel
private theorem c603904 : checkChunk 603904 128 = true := by decide +kernel
private theorem c604032 : checkChunk 604032 128 = true := by decide +kernel
private theorem c604160 : checkChunk 604160 128 = true := by decide +kernel
private theorem c604288 : checkChunk 604288 128 = true := by decide +kernel
private theorem c604416 : checkChunk 604416 128 = true := by decide +kernel
private theorem c604544 : checkChunk 604544 128 = true := by decide +kernel
private theorem c604672 : checkChunk 604672 128 = true := by decide +kernel
private theorem c604800 : checkChunk 604800 128 = true := by decide +kernel
private theorem c604928 : checkChunk 604928 128 = true := by decide +kernel
private theorem c605056 : checkChunk 605056 128 = true := by decide +kernel
private theorem c605184 : checkChunk 605184 128 = true := by decide +kernel
private theorem c605312 : checkChunk 605312 128 = true := by decide +kernel
private theorem c605440 : checkChunk 605440 128 = true := by decide +kernel
private theorem c605568 : checkChunk 605568 128 = true := by decide +kernel
private theorem c605696 : checkChunk 605696 128 = true := by decide +kernel
private theorem c605824 : checkChunk 605824 128 = true := by decide +kernel
private theorem c605952 : checkChunk 605952 128 = true := by decide +kernel
private theorem c606080 : checkChunk 606080 128 = true := by decide +kernel

public theorem checked : Checked 598016 606208 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 598016 128 c598016) (checkChunk_sound 598144 128 c598144)) (Checked.append (checkChunk_sound 598272 128 c598272) (checkChunk_sound 598400 128 c598400))) (Checked.append (Checked.append (checkChunk_sound 598528 128 c598528) (checkChunk_sound 598656 128 c598656)) (Checked.append (checkChunk_sound 598784 128 c598784) (checkChunk_sound 598912 128 c598912)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 599040 128 c599040) (checkChunk_sound 599168 128 c599168)) (Checked.append (checkChunk_sound 599296 128 c599296) (checkChunk_sound 599424 128 c599424))) (Checked.append (Checked.append (checkChunk_sound 599552 128 c599552) (checkChunk_sound 599680 128 c599680)) (Checked.append (checkChunk_sound 599808 128 c599808) (checkChunk_sound 599936 128 c599936))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 600064 128 c600064) (checkChunk_sound 600192 128 c600192)) (Checked.append (checkChunk_sound 600320 128 c600320) (checkChunk_sound 600448 128 c600448))) (Checked.append (Checked.append (checkChunk_sound 600576 128 c600576) (checkChunk_sound 600704 128 c600704)) (Checked.append (checkChunk_sound 600832 128 c600832) (checkChunk_sound 600960 128 c600960)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 601088 128 c601088) (checkChunk_sound 601216 128 c601216)) (Checked.append (checkChunk_sound 601344 128 c601344) (checkChunk_sound 601472 128 c601472))) (Checked.append (Checked.append (checkChunk_sound 601600 128 c601600) (checkChunk_sound 601728 128 c601728)) (Checked.append (checkChunk_sound 601856 128 c601856) (checkChunk_sound 601984 128 c601984)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 602112 128 c602112) (checkChunk_sound 602240 128 c602240)) (Checked.append (checkChunk_sound 602368 128 c602368) (checkChunk_sound 602496 128 c602496))) (Checked.append (Checked.append (checkChunk_sound 602624 128 c602624) (checkChunk_sound 602752 128 c602752)) (Checked.append (checkChunk_sound 602880 128 c602880) (checkChunk_sound 603008 128 c603008)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 603136 128 c603136) (checkChunk_sound 603264 128 c603264)) (Checked.append (checkChunk_sound 603392 128 c603392) (checkChunk_sound 603520 128 c603520))) (Checked.append (Checked.append (checkChunk_sound 603648 128 c603648) (checkChunk_sound 603776 128 c603776)) (Checked.append (checkChunk_sound 603904 128 c603904) (checkChunk_sound 604032 128 c604032))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 604160 128 c604160) (checkChunk_sound 604288 128 c604288)) (Checked.append (checkChunk_sound 604416 128 c604416) (checkChunk_sound 604544 128 c604544))) (Checked.append (Checked.append (checkChunk_sound 604672 128 c604672) (checkChunk_sound 604800 128 c604800)) (Checked.append (checkChunk_sound 604928 128 c604928) (checkChunk_sound 605056 128 c605056)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 605184 128 c605184) (checkChunk_sound 605312 128 c605312)) (Checked.append (checkChunk_sound 605440 128 c605440) (checkChunk_sound 605568 128 c605568))) (Checked.append (Checked.append (checkChunk_sound 605696 128 c605696) (checkChunk_sound 605824 128 c605824)) (Checked.append (checkChunk_sound 605952 128 c605952) (checkChunk_sound 606080 128 c606080)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B020
