module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [40960, 49152).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B004
private theorem c40960 : checkChunk 40960 128 = true := by decide +kernel
private theorem c41088 : checkChunk 41088 128 = true := by decide +kernel
private theorem c41216 : checkChunk 41216 128 = true := by decide +kernel
private theorem c41344 : checkChunk 41344 128 = true := by decide +kernel
private theorem c41472 : checkChunk 41472 128 = true := by decide +kernel
private theorem c41600 : checkChunk 41600 128 = true := by decide +kernel
private theorem c41728 : checkChunk 41728 128 = true := by decide +kernel
private theorem c41856 : checkChunk 41856 128 = true := by decide +kernel
private theorem c41984 : checkChunk 41984 128 = true := by decide +kernel
private theorem c42112 : checkChunk 42112 128 = true := by decide +kernel
private theorem c42240 : checkChunk 42240 128 = true := by decide +kernel
private theorem c42368 : checkChunk 42368 128 = true := by decide +kernel
private theorem c42496 : checkChunk 42496 128 = true := by decide +kernel
private theorem c42624 : checkChunk 42624 128 = true := by decide +kernel
private theorem c42752 : checkChunk 42752 128 = true := by decide +kernel
private theorem c42880 : checkChunk 42880 128 = true := by decide +kernel
private theorem c43008 : checkChunk 43008 128 = true := by decide +kernel
private theorem c43136 : checkChunk 43136 128 = true := by decide +kernel
private theorem c43264 : checkChunk 43264 128 = true := by decide +kernel
private theorem c43392 : checkChunk 43392 128 = true := by decide +kernel
private theorem c43520 : checkChunk 43520 128 = true := by decide +kernel
private theorem c43648 : checkChunk 43648 128 = true := by decide +kernel
private theorem c43776 : checkChunk 43776 128 = true := by decide +kernel
private theorem c43904 : checkChunk 43904 128 = true := by decide +kernel
private theorem c44032 : checkChunk 44032 128 = true := by decide +kernel
private theorem c44160 : checkChunk 44160 128 = true := by decide +kernel
private theorem c44288 : checkChunk 44288 128 = true := by decide +kernel
private theorem c44416 : checkChunk 44416 128 = true := by decide +kernel
private theorem c44544 : checkChunk 44544 128 = true := by decide +kernel
private theorem c44672 : checkChunk 44672 128 = true := by decide +kernel
private theorem c44800 : checkChunk 44800 128 = true := by decide +kernel
private theorem c44928 : checkChunk 44928 128 = true := by decide +kernel
private theorem c45056 : checkChunk 45056 128 = true := by decide +kernel
private theorem c45184 : checkChunk 45184 128 = true := by decide +kernel
private theorem c45312 : checkChunk 45312 128 = true := by decide +kernel
private theorem c45440 : checkChunk 45440 128 = true := by decide +kernel
private theorem c45568 : checkChunk 45568 128 = true := by decide +kernel
private theorem c45696 : checkChunk 45696 128 = true := by decide +kernel
private theorem c45824 : checkChunk 45824 128 = true := by decide +kernel
private theorem c45952 : checkChunk 45952 128 = true := by decide +kernel
private theorem c46080 : checkChunk 46080 128 = true := by decide +kernel
private theorem c46208 : checkChunk 46208 128 = true := by decide +kernel
private theorem c46336 : checkChunk 46336 128 = true := by decide +kernel
private theorem c46464 : checkChunk 46464 128 = true := by decide +kernel
private theorem c46592 : checkChunk 46592 128 = true := by decide +kernel
private theorem c46720 : checkChunk 46720 128 = true := by decide +kernel
private theorem c46848 : checkChunk 46848 128 = true := by decide +kernel
private theorem c46976 : checkChunk 46976 128 = true := by decide +kernel
private theorem c47104 : checkChunk 47104 128 = true := by decide +kernel
private theorem c47232 : checkChunk 47232 128 = true := by decide +kernel
private theorem c47360 : checkChunk 47360 128 = true := by decide +kernel
private theorem c47488 : checkChunk 47488 128 = true := by decide +kernel
private theorem c47616 : checkChunk 47616 128 = true := by decide +kernel
private theorem c47744 : checkChunk 47744 128 = true := by decide +kernel
private theorem c47872 : checkChunk 47872 128 = true := by decide +kernel
private theorem c48000 : checkChunk 48000 128 = true := by decide +kernel
private theorem c48128 : checkChunk 48128 128 = true := by decide +kernel
private theorem c48256 : checkChunk 48256 128 = true := by decide +kernel
private theorem c48384 : checkChunk 48384 128 = true := by decide +kernel
private theorem c48512 : checkChunk 48512 128 = true := by decide +kernel
private theorem c48640 : checkChunk 48640 128 = true := by decide +kernel
private theorem c48768 : checkChunk 48768 128 = true := by decide +kernel
private theorem c48896 : checkChunk 48896 128 = true := by decide +kernel
private theorem c49024 : checkChunk 49024 128 = true := by decide +kernel

public theorem checked : Checked 40960 49152 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 40960 128 c40960) (checkChunk_sound 41088 128 c41088)) (Checked.append (checkChunk_sound 41216 128 c41216) (checkChunk_sound 41344 128 c41344))) (Checked.append (Checked.append (checkChunk_sound 41472 128 c41472) (checkChunk_sound 41600 128 c41600)) (Checked.append (checkChunk_sound 41728 128 c41728) (checkChunk_sound 41856 128 c41856)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 41984 128 c41984) (checkChunk_sound 42112 128 c42112)) (Checked.append (checkChunk_sound 42240 128 c42240) (checkChunk_sound 42368 128 c42368))) (Checked.append (Checked.append (checkChunk_sound 42496 128 c42496) (checkChunk_sound 42624 128 c42624)) (Checked.append (checkChunk_sound 42752 128 c42752) (checkChunk_sound 42880 128 c42880))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 43008 128 c43008) (checkChunk_sound 43136 128 c43136)) (Checked.append (checkChunk_sound 43264 128 c43264) (checkChunk_sound 43392 128 c43392))) (Checked.append (Checked.append (checkChunk_sound 43520 128 c43520) (checkChunk_sound 43648 128 c43648)) (Checked.append (checkChunk_sound 43776 128 c43776) (checkChunk_sound 43904 128 c43904)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 44032 128 c44032) (checkChunk_sound 44160 128 c44160)) (Checked.append (checkChunk_sound 44288 128 c44288) (checkChunk_sound 44416 128 c44416))) (Checked.append (Checked.append (checkChunk_sound 44544 128 c44544) (checkChunk_sound 44672 128 c44672)) (Checked.append (checkChunk_sound 44800 128 c44800) (checkChunk_sound 44928 128 c44928)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 45056 128 c45056) (checkChunk_sound 45184 128 c45184)) (Checked.append (checkChunk_sound 45312 128 c45312) (checkChunk_sound 45440 128 c45440))) (Checked.append (Checked.append (checkChunk_sound 45568 128 c45568) (checkChunk_sound 45696 128 c45696)) (Checked.append (checkChunk_sound 45824 128 c45824) (checkChunk_sound 45952 128 c45952)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 46080 128 c46080) (checkChunk_sound 46208 128 c46208)) (Checked.append (checkChunk_sound 46336 128 c46336) (checkChunk_sound 46464 128 c46464))) (Checked.append (Checked.append (checkChunk_sound 46592 128 c46592) (checkChunk_sound 46720 128 c46720)) (Checked.append (checkChunk_sound 46848 128 c46848) (checkChunk_sound 46976 128 c46976))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 47104 128 c47104) (checkChunk_sound 47232 128 c47232)) (Checked.append (checkChunk_sound 47360 128 c47360) (checkChunk_sound 47488 128 c47488))) (Checked.append (Checked.append (checkChunk_sound 47616 128 c47616) (checkChunk_sound 47744 128 c47744)) (Checked.append (checkChunk_sound 47872 128 c47872) (checkChunk_sound 48000 128 c48000)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 48128 128 c48128) (checkChunk_sound 48256 128 c48256)) (Checked.append (checkChunk_sound 48384 128 c48384) (checkChunk_sound 48512 128 c48512))) (Checked.append (Checked.append (checkChunk_sound 48640 128 c48640) (checkChunk_sound 48768 128 c48768)) (Checked.append (checkChunk_sound 48896 128 c48896) (checkChunk_sound 49024 128 c49024)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B004
