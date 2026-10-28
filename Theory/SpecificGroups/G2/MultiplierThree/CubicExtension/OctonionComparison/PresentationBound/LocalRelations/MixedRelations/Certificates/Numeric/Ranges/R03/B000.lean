module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [647168, 655360).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B000
private theorem c647168 : checkChunk 647168 128 = true := by decide +kernel
private theorem c647296 : checkChunk 647296 128 = true := by decide +kernel
private theorem c647424 : checkChunk 647424 128 = true := by decide +kernel
private theorem c647552 : checkChunk 647552 128 = true := by decide +kernel
private theorem c647680 : checkChunk 647680 128 = true := by decide +kernel
private theorem c647808 : checkChunk 647808 128 = true := by decide +kernel
private theorem c647936 : checkChunk 647936 128 = true := by decide +kernel
private theorem c648064 : checkChunk 648064 128 = true := by decide +kernel
private theorem c648192 : checkChunk 648192 128 = true := by decide +kernel
private theorem c648320 : checkChunk 648320 128 = true := by decide +kernel
private theorem c648448 : checkChunk 648448 128 = true := by decide +kernel
private theorem c648576 : checkChunk 648576 128 = true := by decide +kernel
private theorem c648704 : checkChunk 648704 128 = true := by decide +kernel
private theorem c648832 : checkChunk 648832 128 = true := by decide +kernel
private theorem c648960 : checkChunk 648960 128 = true := by decide +kernel
private theorem c649088 : checkChunk 649088 128 = true := by decide +kernel
private theorem c649216 : checkChunk 649216 128 = true := by decide +kernel
private theorem c649344 : checkChunk 649344 128 = true := by decide +kernel
private theorem c649472 : checkChunk 649472 128 = true := by decide +kernel
private theorem c649600 : checkChunk 649600 128 = true := by decide +kernel
private theorem c649728 : checkChunk 649728 128 = true := by decide +kernel
private theorem c649856 : checkChunk 649856 128 = true := by decide +kernel
private theorem c649984 : checkChunk 649984 128 = true := by decide +kernel
private theorem c650112 : checkChunk 650112 128 = true := by decide +kernel
private theorem c650240 : checkChunk 650240 128 = true := by decide +kernel
private theorem c650368 : checkChunk 650368 128 = true := by decide +kernel
private theorem c650496 : checkChunk 650496 128 = true := by decide +kernel
private theorem c650624 : checkChunk 650624 128 = true := by decide +kernel
private theorem c650752 : checkChunk 650752 128 = true := by decide +kernel
private theorem c650880 : checkChunk 650880 128 = true := by decide +kernel
private theorem c651008 : checkChunk 651008 128 = true := by decide +kernel
private theorem c651136 : checkChunk 651136 128 = true := by decide +kernel
private theorem c651264 : checkChunk 651264 128 = true := by decide +kernel
private theorem c651392 : checkChunk 651392 128 = true := by decide +kernel
private theorem c651520 : checkChunk 651520 128 = true := by decide +kernel
private theorem c651648 : checkChunk 651648 128 = true := by decide +kernel
private theorem c651776 : checkChunk 651776 128 = true := by decide +kernel
private theorem c651904 : checkChunk 651904 128 = true := by decide +kernel
private theorem c652032 : checkChunk 652032 128 = true := by decide +kernel
private theorem c652160 : checkChunk 652160 128 = true := by decide +kernel
private theorem c652288 : checkChunk 652288 128 = true := by decide +kernel
private theorem c652416 : checkChunk 652416 128 = true := by decide +kernel
private theorem c652544 : checkChunk 652544 128 = true := by decide +kernel
private theorem c652672 : checkChunk 652672 128 = true := by decide +kernel
private theorem c652800 : checkChunk 652800 128 = true := by decide +kernel
private theorem c652928 : checkChunk 652928 128 = true := by decide +kernel
private theorem c653056 : checkChunk 653056 128 = true := by decide +kernel
private theorem c653184 : checkChunk 653184 128 = true := by decide +kernel
private theorem c653312 : checkChunk 653312 128 = true := by decide +kernel
private theorem c653440 : checkChunk 653440 128 = true := by decide +kernel
private theorem c653568 : checkChunk 653568 128 = true := by decide +kernel
private theorem c653696 : checkChunk 653696 128 = true := by decide +kernel
private theorem c653824 : checkChunk 653824 128 = true := by decide +kernel
private theorem c653952 : checkChunk 653952 128 = true := by decide +kernel
private theorem c654080 : checkChunk 654080 128 = true := by decide +kernel
private theorem c654208 : checkChunk 654208 128 = true := by decide +kernel
private theorem c654336 : checkChunk 654336 128 = true := by decide +kernel
private theorem c654464 : checkChunk 654464 128 = true := by decide +kernel
private theorem c654592 : checkChunk 654592 128 = true := by decide +kernel
private theorem c654720 : checkChunk 654720 128 = true := by decide +kernel
private theorem c654848 : checkChunk 654848 128 = true := by decide +kernel
private theorem c654976 : checkChunk 654976 128 = true := by decide +kernel
private theorem c655104 : checkChunk 655104 128 = true := by decide +kernel
private theorem c655232 : checkChunk 655232 128 = true := by decide +kernel

public theorem checked : Checked 647168 655360 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 647168 128 c647168) (checkChunk_sound 647296 128 c647296)) (Checked.append (checkChunk_sound 647424 128 c647424) (checkChunk_sound 647552 128 c647552))) (Checked.append (Checked.append (checkChunk_sound 647680 128 c647680) (checkChunk_sound 647808 128 c647808)) (Checked.append (checkChunk_sound 647936 128 c647936) (checkChunk_sound 648064 128 c648064)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 648192 128 c648192) (checkChunk_sound 648320 128 c648320)) (Checked.append (checkChunk_sound 648448 128 c648448) (checkChunk_sound 648576 128 c648576))) (Checked.append (Checked.append (checkChunk_sound 648704 128 c648704) (checkChunk_sound 648832 128 c648832)) (Checked.append (checkChunk_sound 648960 128 c648960) (checkChunk_sound 649088 128 c649088))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 649216 128 c649216) (checkChunk_sound 649344 128 c649344)) (Checked.append (checkChunk_sound 649472 128 c649472) (checkChunk_sound 649600 128 c649600))) (Checked.append (Checked.append (checkChunk_sound 649728 128 c649728) (checkChunk_sound 649856 128 c649856)) (Checked.append (checkChunk_sound 649984 128 c649984) (checkChunk_sound 650112 128 c650112)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 650240 128 c650240) (checkChunk_sound 650368 128 c650368)) (Checked.append (checkChunk_sound 650496 128 c650496) (checkChunk_sound 650624 128 c650624))) (Checked.append (Checked.append (checkChunk_sound 650752 128 c650752) (checkChunk_sound 650880 128 c650880)) (Checked.append (checkChunk_sound 651008 128 c651008) (checkChunk_sound 651136 128 c651136)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 651264 128 c651264) (checkChunk_sound 651392 128 c651392)) (Checked.append (checkChunk_sound 651520 128 c651520) (checkChunk_sound 651648 128 c651648))) (Checked.append (Checked.append (checkChunk_sound 651776 128 c651776) (checkChunk_sound 651904 128 c651904)) (Checked.append (checkChunk_sound 652032 128 c652032) (checkChunk_sound 652160 128 c652160)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 652288 128 c652288) (checkChunk_sound 652416 128 c652416)) (Checked.append (checkChunk_sound 652544 128 c652544) (checkChunk_sound 652672 128 c652672))) (Checked.append (Checked.append (checkChunk_sound 652800 128 c652800) (checkChunk_sound 652928 128 c652928)) (Checked.append (checkChunk_sound 653056 128 c653056) (checkChunk_sound 653184 128 c653184))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 653312 128 c653312) (checkChunk_sound 653440 128 c653440)) (Checked.append (checkChunk_sound 653568 128 c653568) (checkChunk_sound 653696 128 c653696))) (Checked.append (Checked.append (checkChunk_sound 653824 128 c653824) (checkChunk_sound 653952 128 c653952)) (Checked.append (checkChunk_sound 654080 128 c654080) (checkChunk_sound 654208 128 c654208)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 654336 128 c654336) (checkChunk_sound 654464 128 c654464)) (Checked.append (checkChunk_sound 654592 128 c654592) (checkChunk_sound 654720 128 c654720))) (Checked.append (Checked.append (checkChunk_sound 654848 128 c654848) (checkChunk_sound 654976 128 c654976)) (Checked.append (checkChunk_sound 655104 128 c655104) (checkChunk_sound 655232 128 c655232)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B000
