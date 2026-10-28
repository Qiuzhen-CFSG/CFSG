module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [278528, 286720).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B007
private theorem c278528 : checkChunk 278528 128 = true := by decide +kernel
private theorem c278656 : checkChunk 278656 128 = true := by decide +kernel
private theorem c278784 : checkChunk 278784 128 = true := by decide +kernel
private theorem c278912 : checkChunk 278912 128 = true := by decide +kernel
private theorem c279040 : checkChunk 279040 128 = true := by decide +kernel
private theorem c279168 : checkChunk 279168 128 = true := by decide +kernel
private theorem c279296 : checkChunk 279296 128 = true := by decide +kernel
private theorem c279424 : checkChunk 279424 128 = true := by decide +kernel
private theorem c279552 : checkChunk 279552 128 = true := by decide +kernel
private theorem c279680 : checkChunk 279680 128 = true := by decide +kernel
private theorem c279808 : checkChunk 279808 128 = true := by decide +kernel
private theorem c279936 : checkChunk 279936 128 = true := by decide +kernel
private theorem c280064 : checkChunk 280064 128 = true := by decide +kernel
private theorem c280192 : checkChunk 280192 128 = true := by decide +kernel
private theorem c280320 : checkChunk 280320 128 = true := by decide +kernel
private theorem c280448 : checkChunk 280448 128 = true := by decide +kernel
private theorem c280576 : checkChunk 280576 128 = true := by decide +kernel
private theorem c280704 : checkChunk 280704 128 = true := by decide +kernel
private theorem c280832 : checkChunk 280832 128 = true := by decide +kernel
private theorem c280960 : checkChunk 280960 128 = true := by decide +kernel
private theorem c281088 : checkChunk 281088 128 = true := by decide +kernel
private theorem c281216 : checkChunk 281216 128 = true := by decide +kernel
private theorem c281344 : checkChunk 281344 128 = true := by decide +kernel
private theorem c281472 : checkChunk 281472 128 = true := by decide +kernel
private theorem c281600 : checkChunk 281600 128 = true := by decide +kernel
private theorem c281728 : checkChunk 281728 128 = true := by decide +kernel
private theorem c281856 : checkChunk 281856 128 = true := by decide +kernel
private theorem c281984 : checkChunk 281984 128 = true := by decide +kernel
private theorem c282112 : checkChunk 282112 128 = true := by decide +kernel
private theorem c282240 : checkChunk 282240 128 = true := by decide +kernel
private theorem c282368 : checkChunk 282368 128 = true := by decide +kernel
private theorem c282496 : checkChunk 282496 128 = true := by decide +kernel
private theorem c282624 : checkChunk 282624 128 = true := by decide +kernel
private theorem c282752 : checkChunk 282752 128 = true := by decide +kernel
private theorem c282880 : checkChunk 282880 128 = true := by decide +kernel
private theorem c283008 : checkChunk 283008 128 = true := by decide +kernel
private theorem c283136 : checkChunk 283136 128 = true := by decide +kernel
private theorem c283264 : checkChunk 283264 128 = true := by decide +kernel
private theorem c283392 : checkChunk 283392 128 = true := by decide +kernel
private theorem c283520 : checkChunk 283520 128 = true := by decide +kernel
private theorem c283648 : checkChunk 283648 128 = true := by decide +kernel
private theorem c283776 : checkChunk 283776 128 = true := by decide +kernel
private theorem c283904 : checkChunk 283904 128 = true := by decide +kernel
private theorem c284032 : checkChunk 284032 128 = true := by decide +kernel
private theorem c284160 : checkChunk 284160 128 = true := by decide +kernel
private theorem c284288 : checkChunk 284288 128 = true := by decide +kernel
private theorem c284416 : checkChunk 284416 128 = true := by decide +kernel
private theorem c284544 : checkChunk 284544 128 = true := by decide +kernel
private theorem c284672 : checkChunk 284672 128 = true := by decide +kernel
private theorem c284800 : checkChunk 284800 128 = true := by decide +kernel
private theorem c284928 : checkChunk 284928 128 = true := by decide +kernel
private theorem c285056 : checkChunk 285056 128 = true := by decide +kernel
private theorem c285184 : checkChunk 285184 128 = true := by decide +kernel
private theorem c285312 : checkChunk 285312 128 = true := by decide +kernel
private theorem c285440 : checkChunk 285440 128 = true := by decide +kernel
private theorem c285568 : checkChunk 285568 128 = true := by decide +kernel
private theorem c285696 : checkChunk 285696 128 = true := by decide +kernel
private theorem c285824 : checkChunk 285824 128 = true := by decide +kernel
private theorem c285952 : checkChunk 285952 128 = true := by decide +kernel
private theorem c286080 : checkChunk 286080 128 = true := by decide +kernel
private theorem c286208 : checkChunk 286208 128 = true := by decide +kernel
private theorem c286336 : checkChunk 286336 128 = true := by decide +kernel
private theorem c286464 : checkChunk 286464 128 = true := by decide +kernel
private theorem c286592 : checkChunk 286592 128 = true := by decide +kernel

public theorem checked : Checked 278528 286720 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 278528 128 c278528) (checkChunk_sound 278656 128 c278656)) (Checked.append (checkChunk_sound 278784 128 c278784) (checkChunk_sound 278912 128 c278912))) (Checked.append (Checked.append (checkChunk_sound 279040 128 c279040) (checkChunk_sound 279168 128 c279168)) (Checked.append (checkChunk_sound 279296 128 c279296) (checkChunk_sound 279424 128 c279424)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 279552 128 c279552) (checkChunk_sound 279680 128 c279680)) (Checked.append (checkChunk_sound 279808 128 c279808) (checkChunk_sound 279936 128 c279936))) (Checked.append (Checked.append (checkChunk_sound 280064 128 c280064) (checkChunk_sound 280192 128 c280192)) (Checked.append (checkChunk_sound 280320 128 c280320) (checkChunk_sound 280448 128 c280448))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 280576 128 c280576) (checkChunk_sound 280704 128 c280704)) (Checked.append (checkChunk_sound 280832 128 c280832) (checkChunk_sound 280960 128 c280960))) (Checked.append (Checked.append (checkChunk_sound 281088 128 c281088) (checkChunk_sound 281216 128 c281216)) (Checked.append (checkChunk_sound 281344 128 c281344) (checkChunk_sound 281472 128 c281472)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 281600 128 c281600) (checkChunk_sound 281728 128 c281728)) (Checked.append (checkChunk_sound 281856 128 c281856) (checkChunk_sound 281984 128 c281984))) (Checked.append (Checked.append (checkChunk_sound 282112 128 c282112) (checkChunk_sound 282240 128 c282240)) (Checked.append (checkChunk_sound 282368 128 c282368) (checkChunk_sound 282496 128 c282496)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 282624 128 c282624) (checkChunk_sound 282752 128 c282752)) (Checked.append (checkChunk_sound 282880 128 c282880) (checkChunk_sound 283008 128 c283008))) (Checked.append (Checked.append (checkChunk_sound 283136 128 c283136) (checkChunk_sound 283264 128 c283264)) (Checked.append (checkChunk_sound 283392 128 c283392) (checkChunk_sound 283520 128 c283520)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 283648 128 c283648) (checkChunk_sound 283776 128 c283776)) (Checked.append (checkChunk_sound 283904 128 c283904) (checkChunk_sound 284032 128 c284032))) (Checked.append (Checked.append (checkChunk_sound 284160 128 c284160) (checkChunk_sound 284288 128 c284288)) (Checked.append (checkChunk_sound 284416 128 c284416) (checkChunk_sound 284544 128 c284544))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 284672 128 c284672) (checkChunk_sound 284800 128 c284800)) (Checked.append (checkChunk_sound 284928 128 c284928) (checkChunk_sound 285056 128 c285056))) (Checked.append (Checked.append (checkChunk_sound 285184 128 c285184) (checkChunk_sound 285312 128 c285312)) (Checked.append (checkChunk_sound 285440 128 c285440) (checkChunk_sound 285568 128 c285568)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 285696 128 c285696) (checkChunk_sound 285824 128 c285824)) (Checked.append (checkChunk_sound 285952 128 c285952) (checkChunk_sound 286080 128 c286080))) (Checked.append (Checked.append (checkChunk_sound 286208 128 c286208) (checkChunk_sound 286336 128 c286336)) (Checked.append (checkChunk_sound 286464 128 c286464) (checkChunk_sound 286592 128 c286592)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B007
