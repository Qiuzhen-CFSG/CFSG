module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [483328, 491520).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B006
private theorem c483328 : checkChunk 483328 128 = true := by decide +kernel
private theorem c483456 : checkChunk 483456 128 = true := by decide +kernel
private theorem c483584 : checkChunk 483584 128 = true := by decide +kernel
private theorem c483712 : checkChunk 483712 128 = true := by decide +kernel
private theorem c483840 : checkChunk 483840 128 = true := by decide +kernel
private theorem c483968 : checkChunk 483968 128 = true := by decide +kernel
private theorem c484096 : checkChunk 484096 128 = true := by decide +kernel
private theorem c484224 : checkChunk 484224 128 = true := by decide +kernel
private theorem c484352 : checkChunk 484352 128 = true := by decide +kernel
private theorem c484480 : checkChunk 484480 128 = true := by decide +kernel
private theorem c484608 : checkChunk 484608 128 = true := by decide +kernel
private theorem c484736 : checkChunk 484736 128 = true := by decide +kernel
private theorem c484864 : checkChunk 484864 128 = true := by decide +kernel
private theorem c484992 : checkChunk 484992 128 = true := by decide +kernel
private theorem c485120 : checkChunk 485120 128 = true := by decide +kernel
private theorem c485248 : checkChunk 485248 128 = true := by decide +kernel
private theorem c485376 : checkChunk 485376 128 = true := by decide +kernel
private theorem c485504 : checkChunk 485504 128 = true := by decide +kernel
private theorem c485632 : checkChunk 485632 128 = true := by decide +kernel
private theorem c485760 : checkChunk 485760 128 = true := by decide +kernel
private theorem c485888 : checkChunk 485888 128 = true := by decide +kernel
private theorem c486016 : checkChunk 486016 128 = true := by decide +kernel
private theorem c486144 : checkChunk 486144 128 = true := by decide +kernel
private theorem c486272 : checkChunk 486272 128 = true := by decide +kernel
private theorem c486400 : checkChunk 486400 128 = true := by decide +kernel
private theorem c486528 : checkChunk 486528 128 = true := by decide +kernel
private theorem c486656 : checkChunk 486656 128 = true := by decide +kernel
private theorem c486784 : checkChunk 486784 128 = true := by decide +kernel
private theorem c486912 : checkChunk 486912 128 = true := by decide +kernel
private theorem c487040 : checkChunk 487040 128 = true := by decide +kernel
private theorem c487168 : checkChunk 487168 128 = true := by decide +kernel
private theorem c487296 : checkChunk 487296 128 = true := by decide +kernel
private theorem c487424 : checkChunk 487424 128 = true := by decide +kernel
private theorem c487552 : checkChunk 487552 128 = true := by decide +kernel
private theorem c487680 : checkChunk 487680 128 = true := by decide +kernel
private theorem c487808 : checkChunk 487808 128 = true := by decide +kernel
private theorem c487936 : checkChunk 487936 128 = true := by decide +kernel
private theorem c488064 : checkChunk 488064 128 = true := by decide +kernel
private theorem c488192 : checkChunk 488192 128 = true := by decide +kernel
private theorem c488320 : checkChunk 488320 128 = true := by decide +kernel
private theorem c488448 : checkChunk 488448 128 = true := by decide +kernel
private theorem c488576 : checkChunk 488576 128 = true := by decide +kernel
private theorem c488704 : checkChunk 488704 128 = true := by decide +kernel
private theorem c488832 : checkChunk 488832 128 = true := by decide +kernel
private theorem c488960 : checkChunk 488960 128 = true := by decide +kernel
private theorem c489088 : checkChunk 489088 128 = true := by decide +kernel
private theorem c489216 : checkChunk 489216 128 = true := by decide +kernel
private theorem c489344 : checkChunk 489344 128 = true := by decide +kernel
private theorem c489472 : checkChunk 489472 128 = true := by decide +kernel
private theorem c489600 : checkChunk 489600 128 = true := by decide +kernel
private theorem c489728 : checkChunk 489728 128 = true := by decide +kernel
private theorem c489856 : checkChunk 489856 128 = true := by decide +kernel
private theorem c489984 : checkChunk 489984 128 = true := by decide +kernel
private theorem c490112 : checkChunk 490112 128 = true := by decide +kernel
private theorem c490240 : checkChunk 490240 128 = true := by decide +kernel
private theorem c490368 : checkChunk 490368 128 = true := by decide +kernel
private theorem c490496 : checkChunk 490496 128 = true := by decide +kernel
private theorem c490624 : checkChunk 490624 128 = true := by decide +kernel
private theorem c490752 : checkChunk 490752 128 = true := by decide +kernel
private theorem c490880 : checkChunk 490880 128 = true := by decide +kernel
private theorem c491008 : checkChunk 491008 128 = true := by decide +kernel
private theorem c491136 : checkChunk 491136 128 = true := by decide +kernel
private theorem c491264 : checkChunk 491264 128 = true := by decide +kernel
private theorem c491392 : checkChunk 491392 128 = true := by decide +kernel

public theorem checked : Checked 483328 491520 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 483328 128 c483328) (checkChunk_sound 483456 128 c483456)) (Checked.append (checkChunk_sound 483584 128 c483584) (checkChunk_sound 483712 128 c483712))) (Checked.append (Checked.append (checkChunk_sound 483840 128 c483840) (checkChunk_sound 483968 128 c483968)) (Checked.append (checkChunk_sound 484096 128 c484096) (checkChunk_sound 484224 128 c484224)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 484352 128 c484352) (checkChunk_sound 484480 128 c484480)) (Checked.append (checkChunk_sound 484608 128 c484608) (checkChunk_sound 484736 128 c484736))) (Checked.append (Checked.append (checkChunk_sound 484864 128 c484864) (checkChunk_sound 484992 128 c484992)) (Checked.append (checkChunk_sound 485120 128 c485120) (checkChunk_sound 485248 128 c485248))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 485376 128 c485376) (checkChunk_sound 485504 128 c485504)) (Checked.append (checkChunk_sound 485632 128 c485632) (checkChunk_sound 485760 128 c485760))) (Checked.append (Checked.append (checkChunk_sound 485888 128 c485888) (checkChunk_sound 486016 128 c486016)) (Checked.append (checkChunk_sound 486144 128 c486144) (checkChunk_sound 486272 128 c486272)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 486400 128 c486400) (checkChunk_sound 486528 128 c486528)) (Checked.append (checkChunk_sound 486656 128 c486656) (checkChunk_sound 486784 128 c486784))) (Checked.append (Checked.append (checkChunk_sound 486912 128 c486912) (checkChunk_sound 487040 128 c487040)) (Checked.append (checkChunk_sound 487168 128 c487168) (checkChunk_sound 487296 128 c487296)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 487424 128 c487424) (checkChunk_sound 487552 128 c487552)) (Checked.append (checkChunk_sound 487680 128 c487680) (checkChunk_sound 487808 128 c487808))) (Checked.append (Checked.append (checkChunk_sound 487936 128 c487936) (checkChunk_sound 488064 128 c488064)) (Checked.append (checkChunk_sound 488192 128 c488192) (checkChunk_sound 488320 128 c488320)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 488448 128 c488448) (checkChunk_sound 488576 128 c488576)) (Checked.append (checkChunk_sound 488704 128 c488704) (checkChunk_sound 488832 128 c488832))) (Checked.append (Checked.append (checkChunk_sound 488960 128 c488960) (checkChunk_sound 489088 128 c489088)) (Checked.append (checkChunk_sound 489216 128 c489216) (checkChunk_sound 489344 128 c489344))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 489472 128 c489472) (checkChunk_sound 489600 128 c489600)) (Checked.append (checkChunk_sound 489728 128 c489728) (checkChunk_sound 489856 128 c489856))) (Checked.append (Checked.append (checkChunk_sound 489984 128 c489984) (checkChunk_sound 490112 128 c490112)) (Checked.append (checkChunk_sound 490240 128 c490240) (checkChunk_sound 490368 128 c490368)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 490496 128 c490496) (checkChunk_sound 490624 128 c490624)) (Checked.append (checkChunk_sound 490752 128 c490752) (checkChunk_sound 490880 128 c490880))) (Checked.append (Checked.append (checkChunk_sound 491008 128 c491008) (checkChunk_sound 491136 128 c491136)) (Checked.append (checkChunk_sound 491264 128 c491264) (checkChunk_sound 491392 128 c491392)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B006
