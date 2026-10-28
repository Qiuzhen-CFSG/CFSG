module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [163840, 172032).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B019
private theorem c163840 : checkChunk 163840 128 = true := by decide +kernel
private theorem c163968 : checkChunk 163968 128 = true := by decide +kernel
private theorem c164096 : checkChunk 164096 128 = true := by decide +kernel
private theorem c164224 : checkChunk 164224 128 = true := by decide +kernel
private theorem c164352 : checkChunk 164352 128 = true := by decide +kernel
private theorem c164480 : checkChunk 164480 128 = true := by decide +kernel
private theorem c164608 : checkChunk 164608 128 = true := by decide +kernel
private theorem c164736 : checkChunk 164736 128 = true := by decide +kernel
private theorem c164864 : checkChunk 164864 128 = true := by decide +kernel
private theorem c164992 : checkChunk 164992 128 = true := by decide +kernel
private theorem c165120 : checkChunk 165120 128 = true := by decide +kernel
private theorem c165248 : checkChunk 165248 128 = true := by decide +kernel
private theorem c165376 : checkChunk 165376 128 = true := by decide +kernel
private theorem c165504 : checkChunk 165504 128 = true := by decide +kernel
private theorem c165632 : checkChunk 165632 128 = true := by decide +kernel
private theorem c165760 : checkChunk 165760 128 = true := by decide +kernel
private theorem c165888 : checkChunk 165888 128 = true := by decide +kernel
private theorem c166016 : checkChunk 166016 128 = true := by decide +kernel
private theorem c166144 : checkChunk 166144 128 = true := by decide +kernel
private theorem c166272 : checkChunk 166272 128 = true := by decide +kernel
private theorem c166400 : checkChunk 166400 128 = true := by decide +kernel
private theorem c166528 : checkChunk 166528 128 = true := by decide +kernel
private theorem c166656 : checkChunk 166656 128 = true := by decide +kernel
private theorem c166784 : checkChunk 166784 128 = true := by decide +kernel
private theorem c166912 : checkChunk 166912 128 = true := by decide +kernel
private theorem c167040 : checkChunk 167040 128 = true := by decide +kernel
private theorem c167168 : checkChunk 167168 128 = true := by decide +kernel
private theorem c167296 : checkChunk 167296 128 = true := by decide +kernel
private theorem c167424 : checkChunk 167424 128 = true := by decide +kernel
private theorem c167552 : checkChunk 167552 128 = true := by decide +kernel
private theorem c167680 : checkChunk 167680 128 = true := by decide +kernel
private theorem c167808 : checkChunk 167808 128 = true := by decide +kernel
private theorem c167936 : checkChunk 167936 128 = true := by decide +kernel
private theorem c168064 : checkChunk 168064 128 = true := by decide +kernel
private theorem c168192 : checkChunk 168192 128 = true := by decide +kernel
private theorem c168320 : checkChunk 168320 128 = true := by decide +kernel
private theorem c168448 : checkChunk 168448 128 = true := by decide +kernel
private theorem c168576 : checkChunk 168576 128 = true := by decide +kernel
private theorem c168704 : checkChunk 168704 128 = true := by decide +kernel
private theorem c168832 : checkChunk 168832 128 = true := by decide +kernel
private theorem c168960 : checkChunk 168960 128 = true := by decide +kernel
private theorem c169088 : checkChunk 169088 128 = true := by decide +kernel
private theorem c169216 : checkChunk 169216 128 = true := by decide +kernel
private theorem c169344 : checkChunk 169344 128 = true := by decide +kernel
private theorem c169472 : checkChunk 169472 128 = true := by decide +kernel
private theorem c169600 : checkChunk 169600 128 = true := by decide +kernel
private theorem c169728 : checkChunk 169728 128 = true := by decide +kernel
private theorem c169856 : checkChunk 169856 128 = true := by decide +kernel
private theorem c169984 : checkChunk 169984 128 = true := by decide +kernel
private theorem c170112 : checkChunk 170112 128 = true := by decide +kernel
private theorem c170240 : checkChunk 170240 128 = true := by decide +kernel
private theorem c170368 : checkChunk 170368 128 = true := by decide +kernel
private theorem c170496 : checkChunk 170496 128 = true := by decide +kernel
private theorem c170624 : checkChunk 170624 128 = true := by decide +kernel
private theorem c170752 : checkChunk 170752 128 = true := by decide +kernel
private theorem c170880 : checkChunk 170880 128 = true := by decide +kernel
private theorem c171008 : checkChunk 171008 128 = true := by decide +kernel
private theorem c171136 : checkChunk 171136 128 = true := by decide +kernel
private theorem c171264 : checkChunk 171264 128 = true := by decide +kernel
private theorem c171392 : checkChunk 171392 128 = true := by decide +kernel
private theorem c171520 : checkChunk 171520 128 = true := by decide +kernel
private theorem c171648 : checkChunk 171648 128 = true := by decide +kernel
private theorem c171776 : checkChunk 171776 128 = true := by decide +kernel
private theorem c171904 : checkChunk 171904 128 = true := by decide +kernel

public theorem checked : Checked 163840 172032 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 163840 128 c163840) (checkChunk_sound 163968 128 c163968)) (Checked.append (checkChunk_sound 164096 128 c164096) (checkChunk_sound 164224 128 c164224))) (Checked.append (Checked.append (checkChunk_sound 164352 128 c164352) (checkChunk_sound 164480 128 c164480)) (Checked.append (checkChunk_sound 164608 128 c164608) (checkChunk_sound 164736 128 c164736)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 164864 128 c164864) (checkChunk_sound 164992 128 c164992)) (Checked.append (checkChunk_sound 165120 128 c165120) (checkChunk_sound 165248 128 c165248))) (Checked.append (Checked.append (checkChunk_sound 165376 128 c165376) (checkChunk_sound 165504 128 c165504)) (Checked.append (checkChunk_sound 165632 128 c165632) (checkChunk_sound 165760 128 c165760))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 165888 128 c165888) (checkChunk_sound 166016 128 c166016)) (Checked.append (checkChunk_sound 166144 128 c166144) (checkChunk_sound 166272 128 c166272))) (Checked.append (Checked.append (checkChunk_sound 166400 128 c166400) (checkChunk_sound 166528 128 c166528)) (Checked.append (checkChunk_sound 166656 128 c166656) (checkChunk_sound 166784 128 c166784)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 166912 128 c166912) (checkChunk_sound 167040 128 c167040)) (Checked.append (checkChunk_sound 167168 128 c167168) (checkChunk_sound 167296 128 c167296))) (Checked.append (Checked.append (checkChunk_sound 167424 128 c167424) (checkChunk_sound 167552 128 c167552)) (Checked.append (checkChunk_sound 167680 128 c167680) (checkChunk_sound 167808 128 c167808)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 167936 128 c167936) (checkChunk_sound 168064 128 c168064)) (Checked.append (checkChunk_sound 168192 128 c168192) (checkChunk_sound 168320 128 c168320))) (Checked.append (Checked.append (checkChunk_sound 168448 128 c168448) (checkChunk_sound 168576 128 c168576)) (Checked.append (checkChunk_sound 168704 128 c168704) (checkChunk_sound 168832 128 c168832)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 168960 128 c168960) (checkChunk_sound 169088 128 c169088)) (Checked.append (checkChunk_sound 169216 128 c169216) (checkChunk_sound 169344 128 c169344))) (Checked.append (Checked.append (checkChunk_sound 169472 128 c169472) (checkChunk_sound 169600 128 c169600)) (Checked.append (checkChunk_sound 169728 128 c169728) (checkChunk_sound 169856 128 c169856))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 169984 128 c169984) (checkChunk_sound 170112 128 c170112)) (Checked.append (checkChunk_sound 170240 128 c170240) (checkChunk_sound 170368 128 c170368))) (Checked.append (Checked.append (checkChunk_sound 170496 128 c170496) (checkChunk_sound 170624 128 c170624)) (Checked.append (checkChunk_sound 170752 128 c170752) (checkChunk_sound 170880 128 c170880)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 171008 128 c171008) (checkChunk_sound 171136 128 c171136)) (Checked.append (checkChunk_sound 171264 128 c171264) (checkChunk_sound 171392 128 c171392))) (Checked.append (Checked.append (checkChunk_sound 171520 128 c171520) (checkChunk_sound 171648 128 c171648)) (Checked.append (checkChunk_sound 171776 128 c171776) (checkChunk_sound 171904 128 c171904)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B019
