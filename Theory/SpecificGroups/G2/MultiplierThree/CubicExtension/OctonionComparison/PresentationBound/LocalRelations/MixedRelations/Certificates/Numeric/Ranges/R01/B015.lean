module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [344064, 352256).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B015
private theorem c344064 : checkChunk 344064 128 = true := by decide +kernel
private theorem c344192 : checkChunk 344192 128 = true := by decide +kernel
private theorem c344320 : checkChunk 344320 128 = true := by decide +kernel
private theorem c344448 : checkChunk 344448 128 = true := by decide +kernel
private theorem c344576 : checkChunk 344576 128 = true := by decide +kernel
private theorem c344704 : checkChunk 344704 128 = true := by decide +kernel
private theorem c344832 : checkChunk 344832 128 = true := by decide +kernel
private theorem c344960 : checkChunk 344960 128 = true := by decide +kernel
private theorem c345088 : checkChunk 345088 128 = true := by decide +kernel
private theorem c345216 : checkChunk 345216 128 = true := by decide +kernel
private theorem c345344 : checkChunk 345344 128 = true := by decide +kernel
private theorem c345472 : checkChunk 345472 128 = true := by decide +kernel
private theorem c345600 : checkChunk 345600 128 = true := by decide +kernel
private theorem c345728 : checkChunk 345728 128 = true := by decide +kernel
private theorem c345856 : checkChunk 345856 128 = true := by decide +kernel
private theorem c345984 : checkChunk 345984 128 = true := by decide +kernel
private theorem c346112 : checkChunk 346112 128 = true := by decide +kernel
private theorem c346240 : checkChunk 346240 128 = true := by decide +kernel
private theorem c346368 : checkChunk 346368 128 = true := by decide +kernel
private theorem c346496 : checkChunk 346496 128 = true := by decide +kernel
private theorem c346624 : checkChunk 346624 128 = true := by decide +kernel
private theorem c346752 : checkChunk 346752 128 = true := by decide +kernel
private theorem c346880 : checkChunk 346880 128 = true := by decide +kernel
private theorem c347008 : checkChunk 347008 128 = true := by decide +kernel
private theorem c347136 : checkChunk 347136 128 = true := by decide +kernel
private theorem c347264 : checkChunk 347264 128 = true := by decide +kernel
private theorem c347392 : checkChunk 347392 128 = true := by decide +kernel
private theorem c347520 : checkChunk 347520 128 = true := by decide +kernel
private theorem c347648 : checkChunk 347648 128 = true := by decide +kernel
private theorem c347776 : checkChunk 347776 128 = true := by decide +kernel
private theorem c347904 : checkChunk 347904 128 = true := by decide +kernel
private theorem c348032 : checkChunk 348032 128 = true := by decide +kernel
private theorem c348160 : checkChunk 348160 128 = true := by decide +kernel
private theorem c348288 : checkChunk 348288 128 = true := by decide +kernel
private theorem c348416 : checkChunk 348416 128 = true := by decide +kernel
private theorem c348544 : checkChunk 348544 128 = true := by decide +kernel
private theorem c348672 : checkChunk 348672 128 = true := by decide +kernel
private theorem c348800 : checkChunk 348800 128 = true := by decide +kernel
private theorem c348928 : checkChunk 348928 128 = true := by decide +kernel
private theorem c349056 : checkChunk 349056 128 = true := by decide +kernel
private theorem c349184 : checkChunk 349184 128 = true := by decide +kernel
private theorem c349312 : checkChunk 349312 128 = true := by decide +kernel
private theorem c349440 : checkChunk 349440 128 = true := by decide +kernel
private theorem c349568 : checkChunk 349568 128 = true := by decide +kernel
private theorem c349696 : checkChunk 349696 128 = true := by decide +kernel
private theorem c349824 : checkChunk 349824 128 = true := by decide +kernel
private theorem c349952 : checkChunk 349952 128 = true := by decide +kernel
private theorem c350080 : checkChunk 350080 128 = true := by decide +kernel
private theorem c350208 : checkChunk 350208 128 = true := by decide +kernel
private theorem c350336 : checkChunk 350336 128 = true := by decide +kernel
private theorem c350464 : checkChunk 350464 128 = true := by decide +kernel
private theorem c350592 : checkChunk 350592 128 = true := by decide +kernel
private theorem c350720 : checkChunk 350720 128 = true := by decide +kernel
private theorem c350848 : checkChunk 350848 128 = true := by decide +kernel
private theorem c350976 : checkChunk 350976 128 = true := by decide +kernel
private theorem c351104 : checkChunk 351104 128 = true := by decide +kernel
private theorem c351232 : checkChunk 351232 128 = true := by decide +kernel
private theorem c351360 : checkChunk 351360 128 = true := by decide +kernel
private theorem c351488 : checkChunk 351488 128 = true := by decide +kernel
private theorem c351616 : checkChunk 351616 128 = true := by decide +kernel
private theorem c351744 : checkChunk 351744 128 = true := by decide +kernel
private theorem c351872 : checkChunk 351872 128 = true := by decide +kernel
private theorem c352000 : checkChunk 352000 128 = true := by decide +kernel
private theorem c352128 : checkChunk 352128 128 = true := by decide +kernel

public theorem checked : Checked 344064 352256 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 344064 128 c344064) (checkChunk_sound 344192 128 c344192)) (Checked.append (checkChunk_sound 344320 128 c344320) (checkChunk_sound 344448 128 c344448))) (Checked.append (Checked.append (checkChunk_sound 344576 128 c344576) (checkChunk_sound 344704 128 c344704)) (Checked.append (checkChunk_sound 344832 128 c344832) (checkChunk_sound 344960 128 c344960)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 345088 128 c345088) (checkChunk_sound 345216 128 c345216)) (Checked.append (checkChunk_sound 345344 128 c345344) (checkChunk_sound 345472 128 c345472))) (Checked.append (Checked.append (checkChunk_sound 345600 128 c345600) (checkChunk_sound 345728 128 c345728)) (Checked.append (checkChunk_sound 345856 128 c345856) (checkChunk_sound 345984 128 c345984))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 346112 128 c346112) (checkChunk_sound 346240 128 c346240)) (Checked.append (checkChunk_sound 346368 128 c346368) (checkChunk_sound 346496 128 c346496))) (Checked.append (Checked.append (checkChunk_sound 346624 128 c346624) (checkChunk_sound 346752 128 c346752)) (Checked.append (checkChunk_sound 346880 128 c346880) (checkChunk_sound 347008 128 c347008)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 347136 128 c347136) (checkChunk_sound 347264 128 c347264)) (Checked.append (checkChunk_sound 347392 128 c347392) (checkChunk_sound 347520 128 c347520))) (Checked.append (Checked.append (checkChunk_sound 347648 128 c347648) (checkChunk_sound 347776 128 c347776)) (Checked.append (checkChunk_sound 347904 128 c347904) (checkChunk_sound 348032 128 c348032)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 348160 128 c348160) (checkChunk_sound 348288 128 c348288)) (Checked.append (checkChunk_sound 348416 128 c348416) (checkChunk_sound 348544 128 c348544))) (Checked.append (Checked.append (checkChunk_sound 348672 128 c348672) (checkChunk_sound 348800 128 c348800)) (Checked.append (checkChunk_sound 348928 128 c348928) (checkChunk_sound 349056 128 c349056)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 349184 128 c349184) (checkChunk_sound 349312 128 c349312)) (Checked.append (checkChunk_sound 349440 128 c349440) (checkChunk_sound 349568 128 c349568))) (Checked.append (Checked.append (checkChunk_sound 349696 128 c349696) (checkChunk_sound 349824 128 c349824)) (Checked.append (checkChunk_sound 349952 128 c349952) (checkChunk_sound 350080 128 c350080))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 350208 128 c350208) (checkChunk_sound 350336 128 c350336)) (Checked.append (checkChunk_sound 350464 128 c350464) (checkChunk_sound 350592 128 c350592))) (Checked.append (Checked.append (checkChunk_sound 350720 128 c350720) (checkChunk_sound 350848 128 c350848)) (Checked.append (checkChunk_sound 350976 128 c350976) (checkChunk_sound 351104 128 c351104)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 351232 128 c351232) (checkChunk_sound 351360 128 c351360)) (Checked.append (checkChunk_sound 351488 128 c351488) (checkChunk_sound 351616 128 c351616))) (Checked.append (Checked.append (checkChunk_sound 351744 128 c351744) (checkChunk_sound 351872 128 c351872)) (Checked.append (checkChunk_sound 352000 128 c352000) (checkChunk_sound 352128 128 c352128)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B015
