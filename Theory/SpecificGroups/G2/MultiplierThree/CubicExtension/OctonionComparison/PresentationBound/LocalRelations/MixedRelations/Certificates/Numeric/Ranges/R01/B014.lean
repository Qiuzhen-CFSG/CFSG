module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [335872, 344064).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B014
private theorem c335872 : checkChunk 335872 128 = true := by decide +kernel
private theorem c336000 : checkChunk 336000 128 = true := by decide +kernel
private theorem c336128 : checkChunk 336128 128 = true := by decide +kernel
private theorem c336256 : checkChunk 336256 128 = true := by decide +kernel
private theorem c336384 : checkChunk 336384 128 = true := by decide +kernel
private theorem c336512 : checkChunk 336512 128 = true := by decide +kernel
private theorem c336640 : checkChunk 336640 128 = true := by decide +kernel
private theorem c336768 : checkChunk 336768 128 = true := by decide +kernel
private theorem c336896 : checkChunk 336896 128 = true := by decide +kernel
private theorem c337024 : checkChunk 337024 128 = true := by decide +kernel
private theorem c337152 : checkChunk 337152 128 = true := by decide +kernel
private theorem c337280 : checkChunk 337280 128 = true := by decide +kernel
private theorem c337408 : checkChunk 337408 128 = true := by decide +kernel
private theorem c337536 : checkChunk 337536 128 = true := by decide +kernel
private theorem c337664 : checkChunk 337664 128 = true := by decide +kernel
private theorem c337792 : checkChunk 337792 128 = true := by decide +kernel
private theorem c337920 : checkChunk 337920 128 = true := by decide +kernel
private theorem c338048 : checkChunk 338048 128 = true := by decide +kernel
private theorem c338176 : checkChunk 338176 128 = true := by decide +kernel
private theorem c338304 : checkChunk 338304 128 = true := by decide +kernel
private theorem c338432 : checkChunk 338432 128 = true := by decide +kernel
private theorem c338560 : checkChunk 338560 128 = true := by decide +kernel
private theorem c338688 : checkChunk 338688 128 = true := by decide +kernel
private theorem c338816 : checkChunk 338816 128 = true := by decide +kernel
private theorem c338944 : checkChunk 338944 128 = true := by decide +kernel
private theorem c339072 : checkChunk 339072 128 = true := by decide +kernel
private theorem c339200 : checkChunk 339200 128 = true := by decide +kernel
private theorem c339328 : checkChunk 339328 128 = true := by decide +kernel
private theorem c339456 : checkChunk 339456 128 = true := by decide +kernel
private theorem c339584 : checkChunk 339584 128 = true := by decide +kernel
private theorem c339712 : checkChunk 339712 128 = true := by decide +kernel
private theorem c339840 : checkChunk 339840 128 = true := by decide +kernel
private theorem c339968 : checkChunk 339968 128 = true := by decide +kernel
private theorem c340096 : checkChunk 340096 128 = true := by decide +kernel
private theorem c340224 : checkChunk 340224 128 = true := by decide +kernel
private theorem c340352 : checkChunk 340352 128 = true := by decide +kernel
private theorem c340480 : checkChunk 340480 128 = true := by decide +kernel
private theorem c340608 : checkChunk 340608 128 = true := by decide +kernel
private theorem c340736 : checkChunk 340736 128 = true := by decide +kernel
private theorem c340864 : checkChunk 340864 128 = true := by decide +kernel
private theorem c340992 : checkChunk 340992 128 = true := by decide +kernel
private theorem c341120 : checkChunk 341120 128 = true := by decide +kernel
private theorem c341248 : checkChunk 341248 128 = true := by decide +kernel
private theorem c341376 : checkChunk 341376 128 = true := by decide +kernel
private theorem c341504 : checkChunk 341504 128 = true := by decide +kernel
private theorem c341632 : checkChunk 341632 128 = true := by decide +kernel
private theorem c341760 : checkChunk 341760 128 = true := by decide +kernel
private theorem c341888 : checkChunk 341888 128 = true := by decide +kernel
private theorem c342016 : checkChunk 342016 128 = true := by decide +kernel
private theorem c342144 : checkChunk 342144 128 = true := by decide +kernel
private theorem c342272 : checkChunk 342272 128 = true := by decide +kernel
private theorem c342400 : checkChunk 342400 128 = true := by decide +kernel
private theorem c342528 : checkChunk 342528 128 = true := by decide +kernel
private theorem c342656 : checkChunk 342656 128 = true := by decide +kernel
private theorem c342784 : checkChunk 342784 128 = true := by decide +kernel
private theorem c342912 : checkChunk 342912 128 = true := by decide +kernel
private theorem c343040 : checkChunk 343040 128 = true := by decide +kernel
private theorem c343168 : checkChunk 343168 128 = true := by decide +kernel
private theorem c343296 : checkChunk 343296 128 = true := by decide +kernel
private theorem c343424 : checkChunk 343424 128 = true := by decide +kernel
private theorem c343552 : checkChunk 343552 128 = true := by decide +kernel
private theorem c343680 : checkChunk 343680 128 = true := by decide +kernel
private theorem c343808 : checkChunk 343808 128 = true := by decide +kernel
private theorem c343936 : checkChunk 343936 128 = true := by decide +kernel

public theorem checked : Checked 335872 344064 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 335872 128 c335872) (checkChunk_sound 336000 128 c336000)) (Checked.append (checkChunk_sound 336128 128 c336128) (checkChunk_sound 336256 128 c336256))) (Checked.append (Checked.append (checkChunk_sound 336384 128 c336384) (checkChunk_sound 336512 128 c336512)) (Checked.append (checkChunk_sound 336640 128 c336640) (checkChunk_sound 336768 128 c336768)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 336896 128 c336896) (checkChunk_sound 337024 128 c337024)) (Checked.append (checkChunk_sound 337152 128 c337152) (checkChunk_sound 337280 128 c337280))) (Checked.append (Checked.append (checkChunk_sound 337408 128 c337408) (checkChunk_sound 337536 128 c337536)) (Checked.append (checkChunk_sound 337664 128 c337664) (checkChunk_sound 337792 128 c337792))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 337920 128 c337920) (checkChunk_sound 338048 128 c338048)) (Checked.append (checkChunk_sound 338176 128 c338176) (checkChunk_sound 338304 128 c338304))) (Checked.append (Checked.append (checkChunk_sound 338432 128 c338432) (checkChunk_sound 338560 128 c338560)) (Checked.append (checkChunk_sound 338688 128 c338688) (checkChunk_sound 338816 128 c338816)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 338944 128 c338944) (checkChunk_sound 339072 128 c339072)) (Checked.append (checkChunk_sound 339200 128 c339200) (checkChunk_sound 339328 128 c339328))) (Checked.append (Checked.append (checkChunk_sound 339456 128 c339456) (checkChunk_sound 339584 128 c339584)) (Checked.append (checkChunk_sound 339712 128 c339712) (checkChunk_sound 339840 128 c339840)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 339968 128 c339968) (checkChunk_sound 340096 128 c340096)) (Checked.append (checkChunk_sound 340224 128 c340224) (checkChunk_sound 340352 128 c340352))) (Checked.append (Checked.append (checkChunk_sound 340480 128 c340480) (checkChunk_sound 340608 128 c340608)) (Checked.append (checkChunk_sound 340736 128 c340736) (checkChunk_sound 340864 128 c340864)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 340992 128 c340992) (checkChunk_sound 341120 128 c341120)) (Checked.append (checkChunk_sound 341248 128 c341248) (checkChunk_sound 341376 128 c341376))) (Checked.append (Checked.append (checkChunk_sound 341504 128 c341504) (checkChunk_sound 341632 128 c341632)) (Checked.append (checkChunk_sound 341760 128 c341760) (checkChunk_sound 341888 128 c341888))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 342016 128 c342016) (checkChunk_sound 342144 128 c342144)) (Checked.append (checkChunk_sound 342272 128 c342272) (checkChunk_sound 342400 128 c342400))) (Checked.append (Checked.append (checkChunk_sound 342528 128 c342528) (checkChunk_sound 342656 128 c342656)) (Checked.append (checkChunk_sound 342784 128 c342784) (checkChunk_sound 342912 128 c342912)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 343040 128 c343040) (checkChunk_sound 343168 128 c343168)) (Checked.append (checkChunk_sound 343296 128 c343296) (checkChunk_sound 343424 128 c343424))) (Checked.append (Checked.append (checkChunk_sound 343552 128 c343552) (checkChunk_sound 343680 128 c343680)) (Checked.append (checkChunk_sound 343808 128 c343808) (checkChunk_sound 343936 128 c343936)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B014
