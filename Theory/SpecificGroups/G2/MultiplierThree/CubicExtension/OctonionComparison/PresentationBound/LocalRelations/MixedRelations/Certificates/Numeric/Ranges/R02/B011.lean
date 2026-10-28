module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [524288, 532480).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B011
private theorem c524288 : checkChunk 524288 128 = true := by decide +kernel
private theorem c524416 : checkChunk 524416 128 = true := by decide +kernel
private theorem c524544 : checkChunk 524544 128 = true := by decide +kernel
private theorem c524672 : checkChunk 524672 128 = true := by decide +kernel
private theorem c524800 : checkChunk 524800 128 = true := by decide +kernel
private theorem c524928 : checkChunk 524928 128 = true := by decide +kernel
private theorem c525056 : checkChunk 525056 128 = true := by decide +kernel
private theorem c525184 : checkChunk 525184 128 = true := by decide +kernel
private theorem c525312 : checkChunk 525312 128 = true := by decide +kernel
private theorem c525440 : checkChunk 525440 128 = true := by decide +kernel
private theorem c525568 : checkChunk 525568 128 = true := by decide +kernel
private theorem c525696 : checkChunk 525696 128 = true := by decide +kernel
private theorem c525824 : checkChunk 525824 128 = true := by decide +kernel
private theorem c525952 : checkChunk 525952 128 = true := by decide +kernel
private theorem c526080 : checkChunk 526080 128 = true := by decide +kernel
private theorem c526208 : checkChunk 526208 128 = true := by decide +kernel
private theorem c526336 : checkChunk 526336 128 = true := by decide +kernel
private theorem c526464 : checkChunk 526464 128 = true := by decide +kernel
private theorem c526592 : checkChunk 526592 128 = true := by decide +kernel
private theorem c526720 : checkChunk 526720 128 = true := by decide +kernel
private theorem c526848 : checkChunk 526848 128 = true := by decide +kernel
private theorem c526976 : checkChunk 526976 128 = true := by decide +kernel
private theorem c527104 : checkChunk 527104 128 = true := by decide +kernel
private theorem c527232 : checkChunk 527232 128 = true := by decide +kernel
private theorem c527360 : checkChunk 527360 128 = true := by decide +kernel
private theorem c527488 : checkChunk 527488 128 = true := by decide +kernel
private theorem c527616 : checkChunk 527616 128 = true := by decide +kernel
private theorem c527744 : checkChunk 527744 128 = true := by decide +kernel
private theorem c527872 : checkChunk 527872 128 = true := by decide +kernel
private theorem c528000 : checkChunk 528000 128 = true := by decide +kernel
private theorem c528128 : checkChunk 528128 128 = true := by decide +kernel
private theorem c528256 : checkChunk 528256 128 = true := by decide +kernel
private theorem c528384 : checkChunk 528384 128 = true := by decide +kernel
private theorem c528512 : checkChunk 528512 128 = true := by decide +kernel
private theorem c528640 : checkChunk 528640 128 = true := by decide +kernel
private theorem c528768 : checkChunk 528768 128 = true := by decide +kernel
private theorem c528896 : checkChunk 528896 128 = true := by decide +kernel
private theorem c529024 : checkChunk 529024 128 = true := by decide +kernel
private theorem c529152 : checkChunk 529152 128 = true := by decide +kernel
private theorem c529280 : checkChunk 529280 128 = true := by decide +kernel
private theorem c529408 : checkChunk 529408 128 = true := by decide +kernel
private theorem c529536 : checkChunk 529536 128 = true := by decide +kernel
private theorem c529664 : checkChunk 529664 128 = true := by decide +kernel
private theorem c529792 : checkChunk 529792 128 = true := by decide +kernel
private theorem c529920 : checkChunk 529920 128 = true := by decide +kernel
private theorem c530048 : checkChunk 530048 128 = true := by decide +kernel
private theorem c530176 : checkChunk 530176 128 = true := by decide +kernel
private theorem c530304 : checkChunk 530304 128 = true := by decide +kernel
private theorem c530432 : checkChunk 530432 128 = true := by decide +kernel
private theorem c530560 : checkChunk 530560 128 = true := by decide +kernel
private theorem c530688 : checkChunk 530688 128 = true := by decide +kernel
private theorem c530816 : checkChunk 530816 128 = true := by decide +kernel
private theorem c530944 : checkChunk 530944 128 = true := by decide +kernel
private theorem c531072 : checkChunk 531072 128 = true := by decide +kernel
private theorem c531200 : checkChunk 531200 128 = true := by decide +kernel
private theorem c531328 : checkChunk 531328 128 = true := by decide +kernel
private theorem c531456 : checkChunk 531456 128 = true := by decide +kernel
private theorem c531584 : checkChunk 531584 128 = true := by decide +kernel
private theorem c531712 : checkChunk 531712 128 = true := by decide +kernel
private theorem c531840 : checkChunk 531840 128 = true := by decide +kernel
private theorem c531968 : checkChunk 531968 128 = true := by decide +kernel
private theorem c532096 : checkChunk 532096 128 = true := by decide +kernel
private theorem c532224 : checkChunk 532224 128 = true := by decide +kernel
private theorem c532352 : checkChunk 532352 128 = true := by decide +kernel

public theorem checked : Checked 524288 532480 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 524288 128 c524288) (checkChunk_sound 524416 128 c524416)) (Checked.append (checkChunk_sound 524544 128 c524544) (checkChunk_sound 524672 128 c524672))) (Checked.append (Checked.append (checkChunk_sound 524800 128 c524800) (checkChunk_sound 524928 128 c524928)) (Checked.append (checkChunk_sound 525056 128 c525056) (checkChunk_sound 525184 128 c525184)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 525312 128 c525312) (checkChunk_sound 525440 128 c525440)) (Checked.append (checkChunk_sound 525568 128 c525568) (checkChunk_sound 525696 128 c525696))) (Checked.append (Checked.append (checkChunk_sound 525824 128 c525824) (checkChunk_sound 525952 128 c525952)) (Checked.append (checkChunk_sound 526080 128 c526080) (checkChunk_sound 526208 128 c526208))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 526336 128 c526336) (checkChunk_sound 526464 128 c526464)) (Checked.append (checkChunk_sound 526592 128 c526592) (checkChunk_sound 526720 128 c526720))) (Checked.append (Checked.append (checkChunk_sound 526848 128 c526848) (checkChunk_sound 526976 128 c526976)) (Checked.append (checkChunk_sound 527104 128 c527104) (checkChunk_sound 527232 128 c527232)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 527360 128 c527360) (checkChunk_sound 527488 128 c527488)) (Checked.append (checkChunk_sound 527616 128 c527616) (checkChunk_sound 527744 128 c527744))) (Checked.append (Checked.append (checkChunk_sound 527872 128 c527872) (checkChunk_sound 528000 128 c528000)) (Checked.append (checkChunk_sound 528128 128 c528128) (checkChunk_sound 528256 128 c528256)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 528384 128 c528384) (checkChunk_sound 528512 128 c528512)) (Checked.append (checkChunk_sound 528640 128 c528640) (checkChunk_sound 528768 128 c528768))) (Checked.append (Checked.append (checkChunk_sound 528896 128 c528896) (checkChunk_sound 529024 128 c529024)) (Checked.append (checkChunk_sound 529152 128 c529152) (checkChunk_sound 529280 128 c529280)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 529408 128 c529408) (checkChunk_sound 529536 128 c529536)) (Checked.append (checkChunk_sound 529664 128 c529664) (checkChunk_sound 529792 128 c529792))) (Checked.append (Checked.append (checkChunk_sound 529920 128 c529920) (checkChunk_sound 530048 128 c530048)) (Checked.append (checkChunk_sound 530176 128 c530176) (checkChunk_sound 530304 128 c530304))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 530432 128 c530432) (checkChunk_sound 530560 128 c530560)) (Checked.append (checkChunk_sound 530688 128 c530688) (checkChunk_sound 530816 128 c530816))) (Checked.append (Checked.append (checkChunk_sound 530944 128 c530944) (checkChunk_sound 531072 128 c531072)) (Checked.append (checkChunk_sound 531200 128 c531200) (checkChunk_sound 531328 128 c531328)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 531456 128 c531456) (checkChunk_sound 531584 128 c531584)) (Checked.append (checkChunk_sound 531712 128 c531712) (checkChunk_sound 531840 128 c531840))) (Checked.append (Checked.append (checkChunk_sound 531968 128 c531968) (checkChunk_sound 532096 128 c532096)) (Checked.append (checkChunk_sound 532224 128 c532224) (checkChunk_sound 532352 128 c532352)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B011
