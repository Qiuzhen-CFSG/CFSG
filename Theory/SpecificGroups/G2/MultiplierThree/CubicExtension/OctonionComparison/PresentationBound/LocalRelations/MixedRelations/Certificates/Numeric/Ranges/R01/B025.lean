module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [425984, 434176).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B025
private theorem c425984 : checkChunk 425984 128 = true := by decide +kernel
private theorem c426112 : checkChunk 426112 128 = true := by decide +kernel
private theorem c426240 : checkChunk 426240 128 = true := by decide +kernel
private theorem c426368 : checkChunk 426368 128 = true := by decide +kernel
private theorem c426496 : checkChunk 426496 128 = true := by decide +kernel
private theorem c426624 : checkChunk 426624 128 = true := by decide +kernel
private theorem c426752 : checkChunk 426752 128 = true := by decide +kernel
private theorem c426880 : checkChunk 426880 128 = true := by decide +kernel
private theorem c427008 : checkChunk 427008 128 = true := by decide +kernel
private theorem c427136 : checkChunk 427136 128 = true := by decide +kernel
private theorem c427264 : checkChunk 427264 128 = true := by decide +kernel
private theorem c427392 : checkChunk 427392 128 = true := by decide +kernel
private theorem c427520 : checkChunk 427520 128 = true := by decide +kernel
private theorem c427648 : checkChunk 427648 128 = true := by decide +kernel
private theorem c427776 : checkChunk 427776 128 = true := by decide +kernel
private theorem c427904 : checkChunk 427904 128 = true := by decide +kernel
private theorem c428032 : checkChunk 428032 128 = true := by decide +kernel
private theorem c428160 : checkChunk 428160 128 = true := by decide +kernel
private theorem c428288 : checkChunk 428288 128 = true := by decide +kernel
private theorem c428416 : checkChunk 428416 128 = true := by decide +kernel
private theorem c428544 : checkChunk 428544 128 = true := by decide +kernel
private theorem c428672 : checkChunk 428672 128 = true := by decide +kernel
private theorem c428800 : checkChunk 428800 128 = true := by decide +kernel
private theorem c428928 : checkChunk 428928 128 = true := by decide +kernel
private theorem c429056 : checkChunk 429056 128 = true := by decide +kernel
private theorem c429184 : checkChunk 429184 128 = true := by decide +kernel
private theorem c429312 : checkChunk 429312 128 = true := by decide +kernel
private theorem c429440 : checkChunk 429440 128 = true := by decide +kernel
private theorem c429568 : checkChunk 429568 128 = true := by decide +kernel
private theorem c429696 : checkChunk 429696 128 = true := by decide +kernel
private theorem c429824 : checkChunk 429824 128 = true := by decide +kernel
private theorem c429952 : checkChunk 429952 128 = true := by decide +kernel
private theorem c430080 : checkChunk 430080 128 = true := by decide +kernel
private theorem c430208 : checkChunk 430208 128 = true := by decide +kernel
private theorem c430336 : checkChunk 430336 128 = true := by decide +kernel
private theorem c430464 : checkChunk 430464 128 = true := by decide +kernel
private theorem c430592 : checkChunk 430592 128 = true := by decide +kernel
private theorem c430720 : checkChunk 430720 128 = true := by decide +kernel
private theorem c430848 : checkChunk 430848 128 = true := by decide +kernel
private theorem c430976 : checkChunk 430976 128 = true := by decide +kernel
private theorem c431104 : checkChunk 431104 128 = true := by decide +kernel
private theorem c431232 : checkChunk 431232 128 = true := by decide +kernel
private theorem c431360 : checkChunk 431360 128 = true := by decide +kernel
private theorem c431488 : checkChunk 431488 128 = true := by decide +kernel
private theorem c431616 : checkChunk 431616 128 = true := by decide +kernel
private theorem c431744 : checkChunk 431744 128 = true := by decide +kernel
private theorem c431872 : checkChunk 431872 128 = true := by decide +kernel
private theorem c432000 : checkChunk 432000 128 = true := by decide +kernel
private theorem c432128 : checkChunk 432128 128 = true := by decide +kernel
private theorem c432256 : checkChunk 432256 128 = true := by decide +kernel
private theorem c432384 : checkChunk 432384 128 = true := by decide +kernel
private theorem c432512 : checkChunk 432512 128 = true := by decide +kernel
private theorem c432640 : checkChunk 432640 128 = true := by decide +kernel
private theorem c432768 : checkChunk 432768 128 = true := by decide +kernel
private theorem c432896 : checkChunk 432896 128 = true := by decide +kernel
private theorem c433024 : checkChunk 433024 128 = true := by decide +kernel
private theorem c433152 : checkChunk 433152 128 = true := by decide +kernel
private theorem c433280 : checkChunk 433280 128 = true := by decide +kernel
private theorem c433408 : checkChunk 433408 128 = true := by decide +kernel
private theorem c433536 : checkChunk 433536 128 = true := by decide +kernel
private theorem c433664 : checkChunk 433664 128 = true := by decide +kernel
private theorem c433792 : checkChunk 433792 128 = true := by decide +kernel
private theorem c433920 : checkChunk 433920 128 = true := by decide +kernel
private theorem c434048 : checkChunk 434048 128 = true := by decide +kernel

public theorem checked : Checked 425984 434176 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 425984 128 c425984) (checkChunk_sound 426112 128 c426112)) (Checked.append (checkChunk_sound 426240 128 c426240) (checkChunk_sound 426368 128 c426368))) (Checked.append (Checked.append (checkChunk_sound 426496 128 c426496) (checkChunk_sound 426624 128 c426624)) (Checked.append (checkChunk_sound 426752 128 c426752) (checkChunk_sound 426880 128 c426880)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 427008 128 c427008) (checkChunk_sound 427136 128 c427136)) (Checked.append (checkChunk_sound 427264 128 c427264) (checkChunk_sound 427392 128 c427392))) (Checked.append (Checked.append (checkChunk_sound 427520 128 c427520) (checkChunk_sound 427648 128 c427648)) (Checked.append (checkChunk_sound 427776 128 c427776) (checkChunk_sound 427904 128 c427904))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 428032 128 c428032) (checkChunk_sound 428160 128 c428160)) (Checked.append (checkChunk_sound 428288 128 c428288) (checkChunk_sound 428416 128 c428416))) (Checked.append (Checked.append (checkChunk_sound 428544 128 c428544) (checkChunk_sound 428672 128 c428672)) (Checked.append (checkChunk_sound 428800 128 c428800) (checkChunk_sound 428928 128 c428928)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 429056 128 c429056) (checkChunk_sound 429184 128 c429184)) (Checked.append (checkChunk_sound 429312 128 c429312) (checkChunk_sound 429440 128 c429440))) (Checked.append (Checked.append (checkChunk_sound 429568 128 c429568) (checkChunk_sound 429696 128 c429696)) (Checked.append (checkChunk_sound 429824 128 c429824) (checkChunk_sound 429952 128 c429952)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 430080 128 c430080) (checkChunk_sound 430208 128 c430208)) (Checked.append (checkChunk_sound 430336 128 c430336) (checkChunk_sound 430464 128 c430464))) (Checked.append (Checked.append (checkChunk_sound 430592 128 c430592) (checkChunk_sound 430720 128 c430720)) (Checked.append (checkChunk_sound 430848 128 c430848) (checkChunk_sound 430976 128 c430976)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 431104 128 c431104) (checkChunk_sound 431232 128 c431232)) (Checked.append (checkChunk_sound 431360 128 c431360) (checkChunk_sound 431488 128 c431488))) (Checked.append (Checked.append (checkChunk_sound 431616 128 c431616) (checkChunk_sound 431744 128 c431744)) (Checked.append (checkChunk_sound 431872 128 c431872) (checkChunk_sound 432000 128 c432000))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 432128 128 c432128) (checkChunk_sound 432256 128 c432256)) (Checked.append (checkChunk_sound 432384 128 c432384) (checkChunk_sound 432512 128 c432512))) (Checked.append (Checked.append (checkChunk_sound 432640 128 c432640) (checkChunk_sound 432768 128 c432768)) (Checked.append (checkChunk_sound 432896 128 c432896) (checkChunk_sound 433024 128 c433024)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 433152 128 c433152) (checkChunk_sound 433280 128 c433280)) (Checked.append (checkChunk_sound 433408 128 c433408) (checkChunk_sound 433536 128 c433536))) (Checked.append (Checked.append (checkChunk_sound 433664 128 c433664) (checkChunk_sound 433792 128 c433792)) (Checked.append (checkChunk_sound 433920 128 c433920) (checkChunk_sound 434048 128 c434048)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B025
