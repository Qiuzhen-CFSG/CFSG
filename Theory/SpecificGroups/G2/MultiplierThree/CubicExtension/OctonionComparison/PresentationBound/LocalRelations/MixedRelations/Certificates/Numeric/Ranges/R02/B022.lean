module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [614400, 622592).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B022
private theorem c614400 : checkChunk 614400 128 = true := by decide +kernel
private theorem c614528 : checkChunk 614528 128 = true := by decide +kernel
private theorem c614656 : checkChunk 614656 128 = true := by decide +kernel
private theorem c614784 : checkChunk 614784 128 = true := by decide +kernel
private theorem c614912 : checkChunk 614912 128 = true := by decide +kernel
private theorem c615040 : checkChunk 615040 128 = true := by decide +kernel
private theorem c615168 : checkChunk 615168 128 = true := by decide +kernel
private theorem c615296 : checkChunk 615296 128 = true := by decide +kernel
private theorem c615424 : checkChunk 615424 128 = true := by decide +kernel
private theorem c615552 : checkChunk 615552 128 = true := by decide +kernel
private theorem c615680 : checkChunk 615680 128 = true := by decide +kernel
private theorem c615808 : checkChunk 615808 128 = true := by decide +kernel
private theorem c615936 : checkChunk 615936 128 = true := by decide +kernel
private theorem c616064 : checkChunk 616064 128 = true := by decide +kernel
private theorem c616192 : checkChunk 616192 128 = true := by decide +kernel
private theorem c616320 : checkChunk 616320 128 = true := by decide +kernel
private theorem c616448 : checkChunk 616448 128 = true := by decide +kernel
private theorem c616576 : checkChunk 616576 128 = true := by decide +kernel
private theorem c616704 : checkChunk 616704 128 = true := by decide +kernel
private theorem c616832 : checkChunk 616832 128 = true := by decide +kernel
private theorem c616960 : checkChunk 616960 128 = true := by decide +kernel
private theorem c617088 : checkChunk 617088 128 = true := by decide +kernel
private theorem c617216 : checkChunk 617216 128 = true := by decide +kernel
private theorem c617344 : checkChunk 617344 128 = true := by decide +kernel
private theorem c617472 : checkChunk 617472 128 = true := by decide +kernel
private theorem c617600 : checkChunk 617600 128 = true := by decide +kernel
private theorem c617728 : checkChunk 617728 128 = true := by decide +kernel
private theorem c617856 : checkChunk 617856 128 = true := by decide +kernel
private theorem c617984 : checkChunk 617984 128 = true := by decide +kernel
private theorem c618112 : checkChunk 618112 128 = true := by decide +kernel
private theorem c618240 : checkChunk 618240 128 = true := by decide +kernel
private theorem c618368 : checkChunk 618368 128 = true := by decide +kernel
private theorem c618496 : checkChunk 618496 128 = true := by decide +kernel
private theorem c618624 : checkChunk 618624 128 = true := by decide +kernel
private theorem c618752 : checkChunk 618752 128 = true := by decide +kernel
private theorem c618880 : checkChunk 618880 128 = true := by decide +kernel
private theorem c619008 : checkChunk 619008 128 = true := by decide +kernel
private theorem c619136 : checkChunk 619136 128 = true := by decide +kernel
private theorem c619264 : checkChunk 619264 128 = true := by decide +kernel
private theorem c619392 : checkChunk 619392 128 = true := by decide +kernel
private theorem c619520 : checkChunk 619520 128 = true := by decide +kernel
private theorem c619648 : checkChunk 619648 128 = true := by decide +kernel
private theorem c619776 : checkChunk 619776 128 = true := by decide +kernel
private theorem c619904 : checkChunk 619904 128 = true := by decide +kernel
private theorem c620032 : checkChunk 620032 128 = true := by decide +kernel
private theorem c620160 : checkChunk 620160 128 = true := by decide +kernel
private theorem c620288 : checkChunk 620288 128 = true := by decide +kernel
private theorem c620416 : checkChunk 620416 128 = true := by decide +kernel
private theorem c620544 : checkChunk 620544 128 = true := by decide +kernel
private theorem c620672 : checkChunk 620672 128 = true := by decide +kernel
private theorem c620800 : checkChunk 620800 128 = true := by decide +kernel
private theorem c620928 : checkChunk 620928 128 = true := by decide +kernel
private theorem c621056 : checkChunk 621056 128 = true := by decide +kernel
private theorem c621184 : checkChunk 621184 128 = true := by decide +kernel
private theorem c621312 : checkChunk 621312 128 = true := by decide +kernel
private theorem c621440 : checkChunk 621440 128 = true := by decide +kernel
private theorem c621568 : checkChunk 621568 128 = true := by decide +kernel
private theorem c621696 : checkChunk 621696 128 = true := by decide +kernel
private theorem c621824 : checkChunk 621824 128 = true := by decide +kernel
private theorem c621952 : checkChunk 621952 128 = true := by decide +kernel
private theorem c622080 : checkChunk 622080 128 = true := by decide +kernel
private theorem c622208 : checkChunk 622208 128 = true := by decide +kernel
private theorem c622336 : checkChunk 622336 128 = true := by decide +kernel
private theorem c622464 : checkChunk 622464 128 = true := by decide +kernel

public theorem checked : Checked 614400 622592 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 614400 128 c614400) (checkChunk_sound 614528 128 c614528)) (Checked.append (checkChunk_sound 614656 128 c614656) (checkChunk_sound 614784 128 c614784))) (Checked.append (Checked.append (checkChunk_sound 614912 128 c614912) (checkChunk_sound 615040 128 c615040)) (Checked.append (checkChunk_sound 615168 128 c615168) (checkChunk_sound 615296 128 c615296)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 615424 128 c615424) (checkChunk_sound 615552 128 c615552)) (Checked.append (checkChunk_sound 615680 128 c615680) (checkChunk_sound 615808 128 c615808))) (Checked.append (Checked.append (checkChunk_sound 615936 128 c615936) (checkChunk_sound 616064 128 c616064)) (Checked.append (checkChunk_sound 616192 128 c616192) (checkChunk_sound 616320 128 c616320))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 616448 128 c616448) (checkChunk_sound 616576 128 c616576)) (Checked.append (checkChunk_sound 616704 128 c616704) (checkChunk_sound 616832 128 c616832))) (Checked.append (Checked.append (checkChunk_sound 616960 128 c616960) (checkChunk_sound 617088 128 c617088)) (Checked.append (checkChunk_sound 617216 128 c617216) (checkChunk_sound 617344 128 c617344)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 617472 128 c617472) (checkChunk_sound 617600 128 c617600)) (Checked.append (checkChunk_sound 617728 128 c617728) (checkChunk_sound 617856 128 c617856))) (Checked.append (Checked.append (checkChunk_sound 617984 128 c617984) (checkChunk_sound 618112 128 c618112)) (Checked.append (checkChunk_sound 618240 128 c618240) (checkChunk_sound 618368 128 c618368)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 618496 128 c618496) (checkChunk_sound 618624 128 c618624)) (Checked.append (checkChunk_sound 618752 128 c618752) (checkChunk_sound 618880 128 c618880))) (Checked.append (Checked.append (checkChunk_sound 619008 128 c619008) (checkChunk_sound 619136 128 c619136)) (Checked.append (checkChunk_sound 619264 128 c619264) (checkChunk_sound 619392 128 c619392)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 619520 128 c619520) (checkChunk_sound 619648 128 c619648)) (Checked.append (checkChunk_sound 619776 128 c619776) (checkChunk_sound 619904 128 c619904))) (Checked.append (Checked.append (checkChunk_sound 620032 128 c620032) (checkChunk_sound 620160 128 c620160)) (Checked.append (checkChunk_sound 620288 128 c620288) (checkChunk_sound 620416 128 c620416))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 620544 128 c620544) (checkChunk_sound 620672 128 c620672)) (Checked.append (checkChunk_sound 620800 128 c620800) (checkChunk_sound 620928 128 c620928))) (Checked.append (Checked.append (checkChunk_sound 621056 128 c621056) (checkChunk_sound 621184 128 c621184)) (Checked.append (checkChunk_sound 621312 128 c621312) (checkChunk_sound 621440 128 c621440)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 621568 128 c621568) (checkChunk_sound 621696 128 c621696)) (Checked.append (checkChunk_sound 621824 128 c621824) (checkChunk_sound 621952 128 c621952))) (Checked.append (Checked.append (checkChunk_sound 622080 128 c622080) (checkChunk_sound 622208 128 c622208)) (Checked.append (checkChunk_sound 622336 128 c622336) (checkChunk_sound 622464 128 c622464)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B022
