module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [516096, 524288).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B010
private theorem c516096 : checkChunk 516096 128 = true := by decide +kernel
private theorem c516224 : checkChunk 516224 128 = true := by decide +kernel
private theorem c516352 : checkChunk 516352 128 = true := by decide +kernel
private theorem c516480 : checkChunk 516480 128 = true := by decide +kernel
private theorem c516608 : checkChunk 516608 128 = true := by decide +kernel
private theorem c516736 : checkChunk 516736 128 = true := by decide +kernel
private theorem c516864 : checkChunk 516864 128 = true := by decide +kernel
private theorem c516992 : checkChunk 516992 128 = true := by decide +kernel
private theorem c517120 : checkChunk 517120 128 = true := by decide +kernel
private theorem c517248 : checkChunk 517248 128 = true := by decide +kernel
private theorem c517376 : checkChunk 517376 128 = true := by decide +kernel
private theorem c517504 : checkChunk 517504 128 = true := by decide +kernel
private theorem c517632 : checkChunk 517632 128 = true := by decide +kernel
private theorem c517760 : checkChunk 517760 128 = true := by decide +kernel
private theorem c517888 : checkChunk 517888 128 = true := by decide +kernel
private theorem c518016 : checkChunk 518016 128 = true := by decide +kernel
private theorem c518144 : checkChunk 518144 128 = true := by decide +kernel
private theorem c518272 : checkChunk 518272 128 = true := by decide +kernel
private theorem c518400 : checkChunk 518400 128 = true := by decide +kernel
private theorem c518528 : checkChunk 518528 128 = true := by decide +kernel
private theorem c518656 : checkChunk 518656 128 = true := by decide +kernel
private theorem c518784 : checkChunk 518784 128 = true := by decide +kernel
private theorem c518912 : checkChunk 518912 128 = true := by decide +kernel
private theorem c519040 : checkChunk 519040 128 = true := by decide +kernel
private theorem c519168 : checkChunk 519168 128 = true := by decide +kernel
private theorem c519296 : checkChunk 519296 128 = true := by decide +kernel
private theorem c519424 : checkChunk 519424 128 = true := by decide +kernel
private theorem c519552 : checkChunk 519552 128 = true := by decide +kernel
private theorem c519680 : checkChunk 519680 128 = true := by decide +kernel
private theorem c519808 : checkChunk 519808 128 = true := by decide +kernel
private theorem c519936 : checkChunk 519936 128 = true := by decide +kernel
private theorem c520064 : checkChunk 520064 128 = true := by decide +kernel
private theorem c520192 : checkChunk 520192 128 = true := by decide +kernel
private theorem c520320 : checkChunk 520320 128 = true := by decide +kernel
private theorem c520448 : checkChunk 520448 128 = true := by decide +kernel
private theorem c520576 : checkChunk 520576 128 = true := by decide +kernel
private theorem c520704 : checkChunk 520704 128 = true := by decide +kernel
private theorem c520832 : checkChunk 520832 128 = true := by decide +kernel
private theorem c520960 : checkChunk 520960 128 = true := by decide +kernel
private theorem c521088 : checkChunk 521088 128 = true := by decide +kernel
private theorem c521216 : checkChunk 521216 128 = true := by decide +kernel
private theorem c521344 : checkChunk 521344 128 = true := by decide +kernel
private theorem c521472 : checkChunk 521472 128 = true := by decide +kernel
private theorem c521600 : checkChunk 521600 128 = true := by decide +kernel
private theorem c521728 : checkChunk 521728 128 = true := by decide +kernel
private theorem c521856 : checkChunk 521856 128 = true := by decide +kernel
private theorem c521984 : checkChunk 521984 128 = true := by decide +kernel
private theorem c522112 : checkChunk 522112 128 = true := by decide +kernel
private theorem c522240 : checkChunk 522240 128 = true := by decide +kernel
private theorem c522368 : checkChunk 522368 128 = true := by decide +kernel
private theorem c522496 : checkChunk 522496 128 = true := by decide +kernel
private theorem c522624 : checkChunk 522624 128 = true := by decide +kernel
private theorem c522752 : checkChunk 522752 128 = true := by decide +kernel
private theorem c522880 : checkChunk 522880 128 = true := by decide +kernel
private theorem c523008 : checkChunk 523008 128 = true := by decide +kernel
private theorem c523136 : checkChunk 523136 128 = true := by decide +kernel
private theorem c523264 : checkChunk 523264 128 = true := by decide +kernel
private theorem c523392 : checkChunk 523392 128 = true := by decide +kernel
private theorem c523520 : checkChunk 523520 128 = true := by decide +kernel
private theorem c523648 : checkChunk 523648 128 = true := by decide +kernel
private theorem c523776 : checkChunk 523776 128 = true := by decide +kernel
private theorem c523904 : checkChunk 523904 128 = true := by decide +kernel
private theorem c524032 : checkChunk 524032 128 = true := by decide +kernel
private theorem c524160 : checkChunk 524160 128 = true := by decide +kernel

public theorem checked : Checked 516096 524288 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 516096 128 c516096) (checkChunk_sound 516224 128 c516224)) (Checked.append (checkChunk_sound 516352 128 c516352) (checkChunk_sound 516480 128 c516480))) (Checked.append (Checked.append (checkChunk_sound 516608 128 c516608) (checkChunk_sound 516736 128 c516736)) (Checked.append (checkChunk_sound 516864 128 c516864) (checkChunk_sound 516992 128 c516992)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 517120 128 c517120) (checkChunk_sound 517248 128 c517248)) (Checked.append (checkChunk_sound 517376 128 c517376) (checkChunk_sound 517504 128 c517504))) (Checked.append (Checked.append (checkChunk_sound 517632 128 c517632) (checkChunk_sound 517760 128 c517760)) (Checked.append (checkChunk_sound 517888 128 c517888) (checkChunk_sound 518016 128 c518016))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 518144 128 c518144) (checkChunk_sound 518272 128 c518272)) (Checked.append (checkChunk_sound 518400 128 c518400) (checkChunk_sound 518528 128 c518528))) (Checked.append (Checked.append (checkChunk_sound 518656 128 c518656) (checkChunk_sound 518784 128 c518784)) (Checked.append (checkChunk_sound 518912 128 c518912) (checkChunk_sound 519040 128 c519040)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 519168 128 c519168) (checkChunk_sound 519296 128 c519296)) (Checked.append (checkChunk_sound 519424 128 c519424) (checkChunk_sound 519552 128 c519552))) (Checked.append (Checked.append (checkChunk_sound 519680 128 c519680) (checkChunk_sound 519808 128 c519808)) (Checked.append (checkChunk_sound 519936 128 c519936) (checkChunk_sound 520064 128 c520064)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 520192 128 c520192) (checkChunk_sound 520320 128 c520320)) (Checked.append (checkChunk_sound 520448 128 c520448) (checkChunk_sound 520576 128 c520576))) (Checked.append (Checked.append (checkChunk_sound 520704 128 c520704) (checkChunk_sound 520832 128 c520832)) (Checked.append (checkChunk_sound 520960 128 c520960) (checkChunk_sound 521088 128 c521088)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 521216 128 c521216) (checkChunk_sound 521344 128 c521344)) (Checked.append (checkChunk_sound 521472 128 c521472) (checkChunk_sound 521600 128 c521600))) (Checked.append (Checked.append (checkChunk_sound 521728 128 c521728) (checkChunk_sound 521856 128 c521856)) (Checked.append (checkChunk_sound 521984 128 c521984) (checkChunk_sound 522112 128 c522112))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 522240 128 c522240) (checkChunk_sound 522368 128 c522368)) (Checked.append (checkChunk_sound 522496 128 c522496) (checkChunk_sound 522624 128 c522624))) (Checked.append (Checked.append (checkChunk_sound 522752 128 c522752) (checkChunk_sound 522880 128 c522880)) (Checked.append (checkChunk_sound 523008 128 c523008) (checkChunk_sound 523136 128 c523136)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 523264 128 c523264) (checkChunk_sound 523392 128 c523392)) (Checked.append (checkChunk_sound 523520 128 c523520) (checkChunk_sound 523648 128 c523648))) (Checked.append (Checked.append (checkChunk_sound 523776 128 c523776) (checkChunk_sound 523904 128 c523904)) (Checked.append (checkChunk_sound 524032 128 c524032) (checkChunk_sound 524160 128 c524160)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B010
