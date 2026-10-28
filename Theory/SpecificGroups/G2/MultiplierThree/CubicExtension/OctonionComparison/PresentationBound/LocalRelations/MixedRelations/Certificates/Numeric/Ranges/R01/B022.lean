module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [401408, 409600).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B022
private theorem c401408 : checkChunk 401408 128 = true := by decide +kernel
private theorem c401536 : checkChunk 401536 128 = true := by decide +kernel
private theorem c401664 : checkChunk 401664 128 = true := by decide +kernel
private theorem c401792 : checkChunk 401792 128 = true := by decide +kernel
private theorem c401920 : checkChunk 401920 128 = true := by decide +kernel
private theorem c402048 : checkChunk 402048 128 = true := by decide +kernel
private theorem c402176 : checkChunk 402176 128 = true := by decide +kernel
private theorem c402304 : checkChunk 402304 128 = true := by decide +kernel
private theorem c402432 : checkChunk 402432 128 = true := by decide +kernel
private theorem c402560 : checkChunk 402560 128 = true := by decide +kernel
private theorem c402688 : checkChunk 402688 128 = true := by decide +kernel
private theorem c402816 : checkChunk 402816 128 = true := by decide +kernel
private theorem c402944 : checkChunk 402944 128 = true := by decide +kernel
private theorem c403072 : checkChunk 403072 128 = true := by decide +kernel
private theorem c403200 : checkChunk 403200 128 = true := by decide +kernel
private theorem c403328 : checkChunk 403328 128 = true := by decide +kernel
private theorem c403456 : checkChunk 403456 128 = true := by decide +kernel
private theorem c403584 : checkChunk 403584 128 = true := by decide +kernel
private theorem c403712 : checkChunk 403712 128 = true := by decide +kernel
private theorem c403840 : checkChunk 403840 128 = true := by decide +kernel
private theorem c403968 : checkChunk 403968 128 = true := by decide +kernel
private theorem c404096 : checkChunk 404096 128 = true := by decide +kernel
private theorem c404224 : checkChunk 404224 128 = true := by decide +kernel
private theorem c404352 : checkChunk 404352 128 = true := by decide +kernel
private theorem c404480 : checkChunk 404480 128 = true := by decide +kernel
private theorem c404608 : checkChunk 404608 128 = true := by decide +kernel
private theorem c404736 : checkChunk 404736 128 = true := by decide +kernel
private theorem c404864 : checkChunk 404864 128 = true := by decide +kernel
private theorem c404992 : checkChunk 404992 128 = true := by decide +kernel
private theorem c405120 : checkChunk 405120 128 = true := by decide +kernel
private theorem c405248 : checkChunk 405248 128 = true := by decide +kernel
private theorem c405376 : checkChunk 405376 128 = true := by decide +kernel
private theorem c405504 : checkChunk 405504 128 = true := by decide +kernel
private theorem c405632 : checkChunk 405632 128 = true := by decide +kernel
private theorem c405760 : checkChunk 405760 128 = true := by decide +kernel
private theorem c405888 : checkChunk 405888 128 = true := by decide +kernel
private theorem c406016 : checkChunk 406016 128 = true := by decide +kernel
private theorem c406144 : checkChunk 406144 128 = true := by decide +kernel
private theorem c406272 : checkChunk 406272 128 = true := by decide +kernel
private theorem c406400 : checkChunk 406400 128 = true := by decide +kernel
private theorem c406528 : checkChunk 406528 128 = true := by decide +kernel
private theorem c406656 : checkChunk 406656 128 = true := by decide +kernel
private theorem c406784 : checkChunk 406784 128 = true := by decide +kernel
private theorem c406912 : checkChunk 406912 128 = true := by decide +kernel
private theorem c407040 : checkChunk 407040 128 = true := by decide +kernel
private theorem c407168 : checkChunk 407168 128 = true := by decide +kernel
private theorem c407296 : checkChunk 407296 128 = true := by decide +kernel
private theorem c407424 : checkChunk 407424 128 = true := by decide +kernel
private theorem c407552 : checkChunk 407552 128 = true := by decide +kernel
private theorem c407680 : checkChunk 407680 128 = true := by decide +kernel
private theorem c407808 : checkChunk 407808 128 = true := by decide +kernel
private theorem c407936 : checkChunk 407936 128 = true := by decide +kernel
private theorem c408064 : checkChunk 408064 128 = true := by decide +kernel
private theorem c408192 : checkChunk 408192 128 = true := by decide +kernel
private theorem c408320 : checkChunk 408320 128 = true := by decide +kernel
private theorem c408448 : checkChunk 408448 128 = true := by decide +kernel
private theorem c408576 : checkChunk 408576 128 = true := by decide +kernel
private theorem c408704 : checkChunk 408704 128 = true := by decide +kernel
private theorem c408832 : checkChunk 408832 128 = true := by decide +kernel
private theorem c408960 : checkChunk 408960 128 = true := by decide +kernel
private theorem c409088 : checkChunk 409088 128 = true := by decide +kernel
private theorem c409216 : checkChunk 409216 128 = true := by decide +kernel
private theorem c409344 : checkChunk 409344 128 = true := by decide +kernel
private theorem c409472 : checkChunk 409472 128 = true := by decide +kernel

public theorem checked : Checked 401408 409600 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 401408 128 c401408) (checkChunk_sound 401536 128 c401536)) (Checked.append (checkChunk_sound 401664 128 c401664) (checkChunk_sound 401792 128 c401792))) (Checked.append (Checked.append (checkChunk_sound 401920 128 c401920) (checkChunk_sound 402048 128 c402048)) (Checked.append (checkChunk_sound 402176 128 c402176) (checkChunk_sound 402304 128 c402304)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 402432 128 c402432) (checkChunk_sound 402560 128 c402560)) (Checked.append (checkChunk_sound 402688 128 c402688) (checkChunk_sound 402816 128 c402816))) (Checked.append (Checked.append (checkChunk_sound 402944 128 c402944) (checkChunk_sound 403072 128 c403072)) (Checked.append (checkChunk_sound 403200 128 c403200) (checkChunk_sound 403328 128 c403328))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 403456 128 c403456) (checkChunk_sound 403584 128 c403584)) (Checked.append (checkChunk_sound 403712 128 c403712) (checkChunk_sound 403840 128 c403840))) (Checked.append (Checked.append (checkChunk_sound 403968 128 c403968) (checkChunk_sound 404096 128 c404096)) (Checked.append (checkChunk_sound 404224 128 c404224) (checkChunk_sound 404352 128 c404352)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 404480 128 c404480) (checkChunk_sound 404608 128 c404608)) (Checked.append (checkChunk_sound 404736 128 c404736) (checkChunk_sound 404864 128 c404864))) (Checked.append (Checked.append (checkChunk_sound 404992 128 c404992) (checkChunk_sound 405120 128 c405120)) (Checked.append (checkChunk_sound 405248 128 c405248) (checkChunk_sound 405376 128 c405376)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 405504 128 c405504) (checkChunk_sound 405632 128 c405632)) (Checked.append (checkChunk_sound 405760 128 c405760) (checkChunk_sound 405888 128 c405888))) (Checked.append (Checked.append (checkChunk_sound 406016 128 c406016) (checkChunk_sound 406144 128 c406144)) (Checked.append (checkChunk_sound 406272 128 c406272) (checkChunk_sound 406400 128 c406400)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 406528 128 c406528) (checkChunk_sound 406656 128 c406656)) (Checked.append (checkChunk_sound 406784 128 c406784) (checkChunk_sound 406912 128 c406912))) (Checked.append (Checked.append (checkChunk_sound 407040 128 c407040) (checkChunk_sound 407168 128 c407168)) (Checked.append (checkChunk_sound 407296 128 c407296) (checkChunk_sound 407424 128 c407424))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 407552 128 c407552) (checkChunk_sound 407680 128 c407680)) (Checked.append (checkChunk_sound 407808 128 c407808) (checkChunk_sound 407936 128 c407936))) (Checked.append (Checked.append (checkChunk_sound 408064 128 c408064) (checkChunk_sound 408192 128 c408192)) (Checked.append (checkChunk_sound 408320 128 c408320) (checkChunk_sound 408448 128 c408448)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 408576 128 c408576) (checkChunk_sound 408704 128 c408704)) (Checked.append (checkChunk_sound 408832 128 c408832) (checkChunk_sound 408960 128 c408960))) (Checked.append (Checked.append (checkChunk_sound 409088 128 c409088) (checkChunk_sound 409216 128 c409216)) (Checked.append (checkChunk_sound 409344 128 c409344) (checkChunk_sound 409472 128 c409472)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B022
