module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [868352, 876544).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B001
private theorem c868352 : checkChunk 868352 128 = true := by decide +kernel
private theorem c868480 : checkChunk 868480 128 = true := by decide +kernel
private theorem c868608 : checkChunk 868608 128 = true := by decide +kernel
private theorem c868736 : checkChunk 868736 128 = true := by decide +kernel
private theorem c868864 : checkChunk 868864 128 = true := by decide +kernel
private theorem c868992 : checkChunk 868992 128 = true := by decide +kernel
private theorem c869120 : checkChunk 869120 128 = true := by decide +kernel
private theorem c869248 : checkChunk 869248 128 = true := by decide +kernel
private theorem c869376 : checkChunk 869376 128 = true := by decide +kernel
private theorem c869504 : checkChunk 869504 128 = true := by decide +kernel
private theorem c869632 : checkChunk 869632 128 = true := by decide +kernel
private theorem c869760 : checkChunk 869760 128 = true := by decide +kernel
private theorem c869888 : checkChunk 869888 128 = true := by decide +kernel
private theorem c870016 : checkChunk 870016 128 = true := by decide +kernel
private theorem c870144 : checkChunk 870144 128 = true := by decide +kernel
private theorem c870272 : checkChunk 870272 128 = true := by decide +kernel
private theorem c870400 : checkChunk 870400 128 = true := by decide +kernel
private theorem c870528 : checkChunk 870528 128 = true := by decide +kernel
private theorem c870656 : checkChunk 870656 128 = true := by decide +kernel
private theorem c870784 : checkChunk 870784 128 = true := by decide +kernel
private theorem c870912 : checkChunk 870912 128 = true := by decide +kernel
private theorem c871040 : checkChunk 871040 128 = true := by decide +kernel
private theorem c871168 : checkChunk 871168 128 = true := by decide +kernel
private theorem c871296 : checkChunk 871296 128 = true := by decide +kernel
private theorem c871424 : checkChunk 871424 128 = true := by decide +kernel
private theorem c871552 : checkChunk 871552 128 = true := by decide +kernel
private theorem c871680 : checkChunk 871680 128 = true := by decide +kernel
private theorem c871808 : checkChunk 871808 128 = true := by decide +kernel
private theorem c871936 : checkChunk 871936 128 = true := by decide +kernel
private theorem c872064 : checkChunk 872064 128 = true := by decide +kernel
private theorem c872192 : checkChunk 872192 128 = true := by decide +kernel
private theorem c872320 : checkChunk 872320 128 = true := by decide +kernel
private theorem c872448 : checkChunk 872448 128 = true := by decide +kernel
private theorem c872576 : checkChunk 872576 128 = true := by decide +kernel
private theorem c872704 : checkChunk 872704 128 = true := by decide +kernel
private theorem c872832 : checkChunk 872832 128 = true := by decide +kernel
private theorem c872960 : checkChunk 872960 128 = true := by decide +kernel
private theorem c873088 : checkChunk 873088 128 = true := by decide +kernel
private theorem c873216 : checkChunk 873216 128 = true := by decide +kernel
private theorem c873344 : checkChunk 873344 128 = true := by decide +kernel
private theorem c873472 : checkChunk 873472 128 = true := by decide +kernel
private theorem c873600 : checkChunk 873600 128 = true := by decide +kernel
private theorem c873728 : checkChunk 873728 128 = true := by decide +kernel
private theorem c873856 : checkChunk 873856 128 = true := by decide +kernel
private theorem c873984 : checkChunk 873984 128 = true := by decide +kernel
private theorem c874112 : checkChunk 874112 128 = true := by decide +kernel
private theorem c874240 : checkChunk 874240 128 = true := by decide +kernel
private theorem c874368 : checkChunk 874368 128 = true := by decide +kernel
private theorem c874496 : checkChunk 874496 128 = true := by decide +kernel
private theorem c874624 : checkChunk 874624 128 = true := by decide +kernel
private theorem c874752 : checkChunk 874752 128 = true := by decide +kernel
private theorem c874880 : checkChunk 874880 128 = true := by decide +kernel
private theorem c875008 : checkChunk 875008 128 = true := by decide +kernel
private theorem c875136 : checkChunk 875136 128 = true := by decide +kernel
private theorem c875264 : checkChunk 875264 128 = true := by decide +kernel
private theorem c875392 : checkChunk 875392 128 = true := by decide +kernel
private theorem c875520 : checkChunk 875520 128 = true := by decide +kernel
private theorem c875648 : checkChunk 875648 128 = true := by decide +kernel
private theorem c875776 : checkChunk 875776 128 = true := by decide +kernel
private theorem c875904 : checkChunk 875904 128 = true := by decide +kernel
private theorem c876032 : checkChunk 876032 128 = true := by decide +kernel
private theorem c876160 : checkChunk 876160 128 = true := by decide +kernel
private theorem c876288 : checkChunk 876288 128 = true := by decide +kernel
private theorem c876416 : checkChunk 876416 128 = true := by decide +kernel

public theorem checked : Checked 868352 876544 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 868352 128 c868352) (checkChunk_sound 868480 128 c868480)) (Checked.append (checkChunk_sound 868608 128 c868608) (checkChunk_sound 868736 128 c868736))) (Checked.append (Checked.append (checkChunk_sound 868864 128 c868864) (checkChunk_sound 868992 128 c868992)) (Checked.append (checkChunk_sound 869120 128 c869120) (checkChunk_sound 869248 128 c869248)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 869376 128 c869376) (checkChunk_sound 869504 128 c869504)) (Checked.append (checkChunk_sound 869632 128 c869632) (checkChunk_sound 869760 128 c869760))) (Checked.append (Checked.append (checkChunk_sound 869888 128 c869888) (checkChunk_sound 870016 128 c870016)) (Checked.append (checkChunk_sound 870144 128 c870144) (checkChunk_sound 870272 128 c870272))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 870400 128 c870400) (checkChunk_sound 870528 128 c870528)) (Checked.append (checkChunk_sound 870656 128 c870656) (checkChunk_sound 870784 128 c870784))) (Checked.append (Checked.append (checkChunk_sound 870912 128 c870912) (checkChunk_sound 871040 128 c871040)) (Checked.append (checkChunk_sound 871168 128 c871168) (checkChunk_sound 871296 128 c871296)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 871424 128 c871424) (checkChunk_sound 871552 128 c871552)) (Checked.append (checkChunk_sound 871680 128 c871680) (checkChunk_sound 871808 128 c871808))) (Checked.append (Checked.append (checkChunk_sound 871936 128 c871936) (checkChunk_sound 872064 128 c872064)) (Checked.append (checkChunk_sound 872192 128 c872192) (checkChunk_sound 872320 128 c872320)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 872448 128 c872448) (checkChunk_sound 872576 128 c872576)) (Checked.append (checkChunk_sound 872704 128 c872704) (checkChunk_sound 872832 128 c872832))) (Checked.append (Checked.append (checkChunk_sound 872960 128 c872960) (checkChunk_sound 873088 128 c873088)) (Checked.append (checkChunk_sound 873216 128 c873216) (checkChunk_sound 873344 128 c873344)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 873472 128 c873472) (checkChunk_sound 873600 128 c873600)) (Checked.append (checkChunk_sound 873728 128 c873728) (checkChunk_sound 873856 128 c873856))) (Checked.append (Checked.append (checkChunk_sound 873984 128 c873984) (checkChunk_sound 874112 128 c874112)) (Checked.append (checkChunk_sound 874240 128 c874240) (checkChunk_sound 874368 128 c874368))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 874496 128 c874496) (checkChunk_sound 874624 128 c874624)) (Checked.append (checkChunk_sound 874752 128 c874752) (checkChunk_sound 874880 128 c874880))) (Checked.append (Checked.append (checkChunk_sound 875008 128 c875008) (checkChunk_sound 875136 128 c875136)) (Checked.append (checkChunk_sound 875264 128 c875264) (checkChunk_sound 875392 128 c875392)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 875520 128 c875520) (checkChunk_sound 875648 128 c875648)) (Checked.append (checkChunk_sound 875776 128 c875776) (checkChunk_sound 875904 128 c875904))) (Checked.append (Checked.append (checkChunk_sound 876032 128 c876032) (checkChunk_sound 876160 128 c876160)) (Checked.append (checkChunk_sound 876288 128 c876288) (checkChunk_sound 876416 128 c876416)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B001
