module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [475136, 483328).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B005
private theorem c475136 : checkChunk 475136 128 = true := by decide +kernel
private theorem c475264 : checkChunk 475264 128 = true := by decide +kernel
private theorem c475392 : checkChunk 475392 128 = true := by decide +kernel
private theorem c475520 : checkChunk 475520 128 = true := by decide +kernel
private theorem c475648 : checkChunk 475648 128 = true := by decide +kernel
private theorem c475776 : checkChunk 475776 128 = true := by decide +kernel
private theorem c475904 : checkChunk 475904 128 = true := by decide +kernel
private theorem c476032 : checkChunk 476032 128 = true := by decide +kernel
private theorem c476160 : checkChunk 476160 128 = true := by decide +kernel
private theorem c476288 : checkChunk 476288 128 = true := by decide +kernel
private theorem c476416 : checkChunk 476416 128 = true := by decide +kernel
private theorem c476544 : checkChunk 476544 128 = true := by decide +kernel
private theorem c476672 : checkChunk 476672 128 = true := by decide +kernel
private theorem c476800 : checkChunk 476800 128 = true := by decide +kernel
private theorem c476928 : checkChunk 476928 128 = true := by decide +kernel
private theorem c477056 : checkChunk 477056 128 = true := by decide +kernel
private theorem c477184 : checkChunk 477184 128 = true := by decide +kernel
private theorem c477312 : checkChunk 477312 128 = true := by decide +kernel
private theorem c477440 : checkChunk 477440 128 = true := by decide +kernel
private theorem c477568 : checkChunk 477568 128 = true := by decide +kernel
private theorem c477696 : checkChunk 477696 128 = true := by decide +kernel
private theorem c477824 : checkChunk 477824 128 = true := by decide +kernel
private theorem c477952 : checkChunk 477952 128 = true := by decide +kernel
private theorem c478080 : checkChunk 478080 128 = true := by decide +kernel
private theorem c478208 : checkChunk 478208 128 = true := by decide +kernel
private theorem c478336 : checkChunk 478336 128 = true := by decide +kernel
private theorem c478464 : checkChunk 478464 128 = true := by decide +kernel
private theorem c478592 : checkChunk 478592 128 = true := by decide +kernel
private theorem c478720 : checkChunk 478720 128 = true := by decide +kernel
private theorem c478848 : checkChunk 478848 128 = true := by decide +kernel
private theorem c478976 : checkChunk 478976 128 = true := by decide +kernel
private theorem c479104 : checkChunk 479104 128 = true := by decide +kernel
private theorem c479232 : checkChunk 479232 128 = true := by decide +kernel
private theorem c479360 : checkChunk 479360 128 = true := by decide +kernel
private theorem c479488 : checkChunk 479488 128 = true := by decide +kernel
private theorem c479616 : checkChunk 479616 128 = true := by decide +kernel
private theorem c479744 : checkChunk 479744 128 = true := by decide +kernel
private theorem c479872 : checkChunk 479872 128 = true := by decide +kernel
private theorem c480000 : checkChunk 480000 128 = true := by decide +kernel
private theorem c480128 : checkChunk 480128 128 = true := by decide +kernel
private theorem c480256 : checkChunk 480256 128 = true := by decide +kernel
private theorem c480384 : checkChunk 480384 128 = true := by decide +kernel
private theorem c480512 : checkChunk 480512 128 = true := by decide +kernel
private theorem c480640 : checkChunk 480640 128 = true := by decide +kernel
private theorem c480768 : checkChunk 480768 128 = true := by decide +kernel
private theorem c480896 : checkChunk 480896 128 = true := by decide +kernel
private theorem c481024 : checkChunk 481024 128 = true := by decide +kernel
private theorem c481152 : checkChunk 481152 128 = true := by decide +kernel
private theorem c481280 : checkChunk 481280 128 = true := by decide +kernel
private theorem c481408 : checkChunk 481408 128 = true := by decide +kernel
private theorem c481536 : checkChunk 481536 128 = true := by decide +kernel
private theorem c481664 : checkChunk 481664 128 = true := by decide +kernel
private theorem c481792 : checkChunk 481792 128 = true := by decide +kernel
private theorem c481920 : checkChunk 481920 128 = true := by decide +kernel
private theorem c482048 : checkChunk 482048 128 = true := by decide +kernel
private theorem c482176 : checkChunk 482176 128 = true := by decide +kernel
private theorem c482304 : checkChunk 482304 128 = true := by decide +kernel
private theorem c482432 : checkChunk 482432 128 = true := by decide +kernel
private theorem c482560 : checkChunk 482560 128 = true := by decide +kernel
private theorem c482688 : checkChunk 482688 128 = true := by decide +kernel
private theorem c482816 : checkChunk 482816 128 = true := by decide +kernel
private theorem c482944 : checkChunk 482944 128 = true := by decide +kernel
private theorem c483072 : checkChunk 483072 128 = true := by decide +kernel
private theorem c483200 : checkChunk 483200 128 = true := by decide +kernel

public theorem checked : Checked 475136 483328 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 475136 128 c475136) (checkChunk_sound 475264 128 c475264)) (Checked.append (checkChunk_sound 475392 128 c475392) (checkChunk_sound 475520 128 c475520))) (Checked.append (Checked.append (checkChunk_sound 475648 128 c475648) (checkChunk_sound 475776 128 c475776)) (Checked.append (checkChunk_sound 475904 128 c475904) (checkChunk_sound 476032 128 c476032)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 476160 128 c476160) (checkChunk_sound 476288 128 c476288)) (Checked.append (checkChunk_sound 476416 128 c476416) (checkChunk_sound 476544 128 c476544))) (Checked.append (Checked.append (checkChunk_sound 476672 128 c476672) (checkChunk_sound 476800 128 c476800)) (Checked.append (checkChunk_sound 476928 128 c476928) (checkChunk_sound 477056 128 c477056))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 477184 128 c477184) (checkChunk_sound 477312 128 c477312)) (Checked.append (checkChunk_sound 477440 128 c477440) (checkChunk_sound 477568 128 c477568))) (Checked.append (Checked.append (checkChunk_sound 477696 128 c477696) (checkChunk_sound 477824 128 c477824)) (Checked.append (checkChunk_sound 477952 128 c477952) (checkChunk_sound 478080 128 c478080)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 478208 128 c478208) (checkChunk_sound 478336 128 c478336)) (Checked.append (checkChunk_sound 478464 128 c478464) (checkChunk_sound 478592 128 c478592))) (Checked.append (Checked.append (checkChunk_sound 478720 128 c478720) (checkChunk_sound 478848 128 c478848)) (Checked.append (checkChunk_sound 478976 128 c478976) (checkChunk_sound 479104 128 c479104)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 479232 128 c479232) (checkChunk_sound 479360 128 c479360)) (Checked.append (checkChunk_sound 479488 128 c479488) (checkChunk_sound 479616 128 c479616))) (Checked.append (Checked.append (checkChunk_sound 479744 128 c479744) (checkChunk_sound 479872 128 c479872)) (Checked.append (checkChunk_sound 480000 128 c480000) (checkChunk_sound 480128 128 c480128)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 480256 128 c480256) (checkChunk_sound 480384 128 c480384)) (Checked.append (checkChunk_sound 480512 128 c480512) (checkChunk_sound 480640 128 c480640))) (Checked.append (Checked.append (checkChunk_sound 480768 128 c480768) (checkChunk_sound 480896 128 c480896)) (Checked.append (checkChunk_sound 481024 128 c481024) (checkChunk_sound 481152 128 c481152))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 481280 128 c481280) (checkChunk_sound 481408 128 c481408)) (Checked.append (checkChunk_sound 481536 128 c481536) (checkChunk_sound 481664 128 c481664))) (Checked.append (Checked.append (checkChunk_sound 481792 128 c481792) (checkChunk_sound 481920 128 c481920)) (Checked.append (checkChunk_sound 482048 128 c482048) (checkChunk_sound 482176 128 c482176)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 482304 128 c482304) (checkChunk_sound 482432 128 c482432)) (Checked.append (checkChunk_sound 482560 128 c482560) (checkChunk_sound 482688 128 c482688))) (Checked.append (Checked.append (checkChunk_sound 482816 128 c482816) (checkChunk_sound 482944 128 c482944)) (Checked.append (checkChunk_sound 483072 128 c483072) (checkChunk_sound 483200 128 c483200)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B005
