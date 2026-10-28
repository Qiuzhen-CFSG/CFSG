module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1540096, 1548288).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B005
private theorem c1540096 : checkChunk 1540096 128 = true := by decide +kernel
private theorem c1540224 : checkChunk 1540224 128 = true := by decide +kernel
private theorem c1540352 : checkChunk 1540352 128 = true := by decide +kernel
private theorem c1540480 : checkChunk 1540480 128 = true := by decide +kernel
private theorem c1540608 : checkChunk 1540608 128 = true := by decide +kernel
private theorem c1540736 : checkChunk 1540736 128 = true := by decide +kernel
private theorem c1540864 : checkChunk 1540864 128 = true := by decide +kernel
private theorem c1540992 : checkChunk 1540992 128 = true := by decide +kernel
private theorem c1541120 : checkChunk 1541120 128 = true := by decide +kernel
private theorem c1541248 : checkChunk 1541248 128 = true := by decide +kernel
private theorem c1541376 : checkChunk 1541376 128 = true := by decide +kernel
private theorem c1541504 : checkChunk 1541504 128 = true := by decide +kernel
private theorem c1541632 : checkChunk 1541632 128 = true := by decide +kernel
private theorem c1541760 : checkChunk 1541760 128 = true := by decide +kernel
private theorem c1541888 : checkChunk 1541888 128 = true := by decide +kernel
private theorem c1542016 : checkChunk 1542016 128 = true := by decide +kernel
private theorem c1542144 : checkChunk 1542144 128 = true := by decide +kernel
private theorem c1542272 : checkChunk 1542272 128 = true := by decide +kernel
private theorem c1542400 : checkChunk 1542400 128 = true := by decide +kernel
private theorem c1542528 : checkChunk 1542528 128 = true := by decide +kernel
private theorem c1542656 : checkChunk 1542656 128 = true := by decide +kernel
private theorem c1542784 : checkChunk 1542784 128 = true := by decide +kernel
private theorem c1542912 : checkChunk 1542912 128 = true := by decide +kernel
private theorem c1543040 : checkChunk 1543040 128 = true := by decide +kernel
private theorem c1543168 : checkChunk 1543168 128 = true := by decide +kernel
private theorem c1543296 : checkChunk 1543296 128 = true := by decide +kernel
private theorem c1543424 : checkChunk 1543424 128 = true := by decide +kernel
private theorem c1543552 : checkChunk 1543552 128 = true := by decide +kernel
private theorem c1543680 : checkChunk 1543680 128 = true := by decide +kernel
private theorem c1543808 : checkChunk 1543808 128 = true := by decide +kernel
private theorem c1543936 : checkChunk 1543936 128 = true := by decide +kernel
private theorem c1544064 : checkChunk 1544064 128 = true := by decide +kernel
private theorem c1544192 : checkChunk 1544192 128 = true := by decide +kernel
private theorem c1544320 : checkChunk 1544320 128 = true := by decide +kernel
private theorem c1544448 : checkChunk 1544448 128 = true := by decide +kernel
private theorem c1544576 : checkChunk 1544576 128 = true := by decide +kernel
private theorem c1544704 : checkChunk 1544704 128 = true := by decide +kernel
private theorem c1544832 : checkChunk 1544832 128 = true := by decide +kernel
private theorem c1544960 : checkChunk 1544960 128 = true := by decide +kernel
private theorem c1545088 : checkChunk 1545088 128 = true := by decide +kernel
private theorem c1545216 : checkChunk 1545216 128 = true := by decide +kernel
private theorem c1545344 : checkChunk 1545344 128 = true := by decide +kernel
private theorem c1545472 : checkChunk 1545472 128 = true := by decide +kernel
private theorem c1545600 : checkChunk 1545600 128 = true := by decide +kernel
private theorem c1545728 : checkChunk 1545728 128 = true := by decide +kernel
private theorem c1545856 : checkChunk 1545856 128 = true := by decide +kernel
private theorem c1545984 : checkChunk 1545984 128 = true := by decide +kernel
private theorem c1546112 : checkChunk 1546112 128 = true := by decide +kernel
private theorem c1546240 : checkChunk 1546240 128 = true := by decide +kernel
private theorem c1546368 : checkChunk 1546368 128 = true := by decide +kernel
private theorem c1546496 : checkChunk 1546496 128 = true := by decide +kernel
private theorem c1546624 : checkChunk 1546624 128 = true := by decide +kernel
private theorem c1546752 : checkChunk 1546752 128 = true := by decide +kernel
private theorem c1546880 : checkChunk 1546880 128 = true := by decide +kernel
private theorem c1547008 : checkChunk 1547008 128 = true := by decide +kernel
private theorem c1547136 : checkChunk 1547136 128 = true := by decide +kernel
private theorem c1547264 : checkChunk 1547264 128 = true := by decide +kernel
private theorem c1547392 : checkChunk 1547392 128 = true := by decide +kernel
private theorem c1547520 : checkChunk 1547520 128 = true := by decide +kernel
private theorem c1547648 : checkChunk 1547648 128 = true := by decide +kernel
private theorem c1547776 : checkChunk 1547776 128 = true := by decide +kernel
private theorem c1547904 : checkChunk 1547904 128 = true := by decide +kernel
private theorem c1548032 : checkChunk 1548032 128 = true := by decide +kernel
private theorem c1548160 : checkChunk 1548160 128 = true := by decide +kernel

public theorem checked : Checked 1540096 1548288 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1540096 128 c1540096) (checkChunk_sound 1540224 128 c1540224)) (Checked.append (checkChunk_sound 1540352 128 c1540352) (checkChunk_sound 1540480 128 c1540480))) (Checked.append (Checked.append (checkChunk_sound 1540608 128 c1540608) (checkChunk_sound 1540736 128 c1540736)) (Checked.append (checkChunk_sound 1540864 128 c1540864) (checkChunk_sound 1540992 128 c1540992)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1541120 128 c1541120) (checkChunk_sound 1541248 128 c1541248)) (Checked.append (checkChunk_sound 1541376 128 c1541376) (checkChunk_sound 1541504 128 c1541504))) (Checked.append (Checked.append (checkChunk_sound 1541632 128 c1541632) (checkChunk_sound 1541760 128 c1541760)) (Checked.append (checkChunk_sound 1541888 128 c1541888) (checkChunk_sound 1542016 128 c1542016))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1542144 128 c1542144) (checkChunk_sound 1542272 128 c1542272)) (Checked.append (checkChunk_sound 1542400 128 c1542400) (checkChunk_sound 1542528 128 c1542528))) (Checked.append (Checked.append (checkChunk_sound 1542656 128 c1542656) (checkChunk_sound 1542784 128 c1542784)) (Checked.append (checkChunk_sound 1542912 128 c1542912) (checkChunk_sound 1543040 128 c1543040)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1543168 128 c1543168) (checkChunk_sound 1543296 128 c1543296)) (Checked.append (checkChunk_sound 1543424 128 c1543424) (checkChunk_sound 1543552 128 c1543552))) (Checked.append (Checked.append (checkChunk_sound 1543680 128 c1543680) (checkChunk_sound 1543808 128 c1543808)) (Checked.append (checkChunk_sound 1543936 128 c1543936) (checkChunk_sound 1544064 128 c1544064)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1544192 128 c1544192) (checkChunk_sound 1544320 128 c1544320)) (Checked.append (checkChunk_sound 1544448 128 c1544448) (checkChunk_sound 1544576 128 c1544576))) (Checked.append (Checked.append (checkChunk_sound 1544704 128 c1544704) (checkChunk_sound 1544832 128 c1544832)) (Checked.append (checkChunk_sound 1544960 128 c1544960) (checkChunk_sound 1545088 128 c1545088)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1545216 128 c1545216) (checkChunk_sound 1545344 128 c1545344)) (Checked.append (checkChunk_sound 1545472 128 c1545472) (checkChunk_sound 1545600 128 c1545600))) (Checked.append (Checked.append (checkChunk_sound 1545728 128 c1545728) (checkChunk_sound 1545856 128 c1545856)) (Checked.append (checkChunk_sound 1545984 128 c1545984) (checkChunk_sound 1546112 128 c1546112))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1546240 128 c1546240) (checkChunk_sound 1546368 128 c1546368)) (Checked.append (checkChunk_sound 1546496 128 c1546496) (checkChunk_sound 1546624 128 c1546624))) (Checked.append (Checked.append (checkChunk_sound 1546752 128 c1546752) (checkChunk_sound 1546880 128 c1546880)) (Checked.append (checkChunk_sound 1547008 128 c1547008) (checkChunk_sound 1547136 128 c1547136)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1547264 128 c1547264) (checkChunk_sound 1547392 128 c1547392)) (Checked.append (checkChunk_sound 1547520 128 c1547520) (checkChunk_sound 1547648 128 c1547648))) (Checked.append (Checked.append (checkChunk_sound 1547776 128 c1547776) (checkChunk_sound 1547904 128 c1547904)) (Checked.append (checkChunk_sound 1548032 128 c1548032) (checkChunk_sound 1548160 128 c1548160)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B005
