module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [417792, 425984).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B024
private theorem c417792 : checkChunk 417792 128 = true := by decide +kernel
private theorem c417920 : checkChunk 417920 128 = true := by decide +kernel
private theorem c418048 : checkChunk 418048 128 = true := by decide +kernel
private theorem c418176 : checkChunk 418176 128 = true := by decide +kernel
private theorem c418304 : checkChunk 418304 128 = true := by decide +kernel
private theorem c418432 : checkChunk 418432 128 = true := by decide +kernel
private theorem c418560 : checkChunk 418560 128 = true := by decide +kernel
private theorem c418688 : checkChunk 418688 128 = true := by decide +kernel
private theorem c418816 : checkChunk 418816 128 = true := by decide +kernel
private theorem c418944 : checkChunk 418944 128 = true := by decide +kernel
private theorem c419072 : checkChunk 419072 128 = true := by decide +kernel
private theorem c419200 : checkChunk 419200 128 = true := by decide +kernel
private theorem c419328 : checkChunk 419328 128 = true := by decide +kernel
private theorem c419456 : checkChunk 419456 128 = true := by decide +kernel
private theorem c419584 : checkChunk 419584 128 = true := by decide +kernel
private theorem c419712 : checkChunk 419712 128 = true := by decide +kernel
private theorem c419840 : checkChunk 419840 128 = true := by decide +kernel
private theorem c419968 : checkChunk 419968 128 = true := by decide +kernel
private theorem c420096 : checkChunk 420096 128 = true := by decide +kernel
private theorem c420224 : checkChunk 420224 128 = true := by decide +kernel
private theorem c420352 : checkChunk 420352 128 = true := by decide +kernel
private theorem c420480 : checkChunk 420480 128 = true := by decide +kernel
private theorem c420608 : checkChunk 420608 128 = true := by decide +kernel
private theorem c420736 : checkChunk 420736 128 = true := by decide +kernel
private theorem c420864 : checkChunk 420864 128 = true := by decide +kernel
private theorem c420992 : checkChunk 420992 128 = true := by decide +kernel
private theorem c421120 : checkChunk 421120 128 = true := by decide +kernel
private theorem c421248 : checkChunk 421248 128 = true := by decide +kernel
private theorem c421376 : checkChunk 421376 128 = true := by decide +kernel
private theorem c421504 : checkChunk 421504 128 = true := by decide +kernel
private theorem c421632 : checkChunk 421632 128 = true := by decide +kernel
private theorem c421760 : checkChunk 421760 128 = true := by decide +kernel
private theorem c421888 : checkChunk 421888 128 = true := by decide +kernel
private theorem c422016 : checkChunk 422016 128 = true := by decide +kernel
private theorem c422144 : checkChunk 422144 128 = true := by decide +kernel
private theorem c422272 : checkChunk 422272 128 = true := by decide +kernel
private theorem c422400 : checkChunk 422400 128 = true := by decide +kernel
private theorem c422528 : checkChunk 422528 128 = true := by decide +kernel
private theorem c422656 : checkChunk 422656 128 = true := by decide +kernel
private theorem c422784 : checkChunk 422784 128 = true := by decide +kernel
private theorem c422912 : checkChunk 422912 128 = true := by decide +kernel
private theorem c423040 : checkChunk 423040 128 = true := by decide +kernel
private theorem c423168 : checkChunk 423168 128 = true := by decide +kernel
private theorem c423296 : checkChunk 423296 128 = true := by decide +kernel
private theorem c423424 : checkChunk 423424 128 = true := by decide +kernel
private theorem c423552 : checkChunk 423552 128 = true := by decide +kernel
private theorem c423680 : checkChunk 423680 128 = true := by decide +kernel
private theorem c423808 : checkChunk 423808 128 = true := by decide +kernel
private theorem c423936 : checkChunk 423936 128 = true := by decide +kernel
private theorem c424064 : checkChunk 424064 128 = true := by decide +kernel
private theorem c424192 : checkChunk 424192 128 = true := by decide +kernel
private theorem c424320 : checkChunk 424320 128 = true := by decide +kernel
private theorem c424448 : checkChunk 424448 128 = true := by decide +kernel
private theorem c424576 : checkChunk 424576 128 = true := by decide +kernel
private theorem c424704 : checkChunk 424704 128 = true := by decide +kernel
private theorem c424832 : checkChunk 424832 128 = true := by decide +kernel
private theorem c424960 : checkChunk 424960 128 = true := by decide +kernel
private theorem c425088 : checkChunk 425088 128 = true := by decide +kernel
private theorem c425216 : checkChunk 425216 128 = true := by decide +kernel
private theorem c425344 : checkChunk 425344 128 = true := by decide +kernel
private theorem c425472 : checkChunk 425472 128 = true := by decide +kernel
private theorem c425600 : checkChunk 425600 128 = true := by decide +kernel
private theorem c425728 : checkChunk 425728 128 = true := by decide +kernel
private theorem c425856 : checkChunk 425856 128 = true := by decide +kernel

public theorem checked : Checked 417792 425984 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 417792 128 c417792) (checkChunk_sound 417920 128 c417920)) (Checked.append (checkChunk_sound 418048 128 c418048) (checkChunk_sound 418176 128 c418176))) (Checked.append (Checked.append (checkChunk_sound 418304 128 c418304) (checkChunk_sound 418432 128 c418432)) (Checked.append (checkChunk_sound 418560 128 c418560) (checkChunk_sound 418688 128 c418688)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 418816 128 c418816) (checkChunk_sound 418944 128 c418944)) (Checked.append (checkChunk_sound 419072 128 c419072) (checkChunk_sound 419200 128 c419200))) (Checked.append (Checked.append (checkChunk_sound 419328 128 c419328) (checkChunk_sound 419456 128 c419456)) (Checked.append (checkChunk_sound 419584 128 c419584) (checkChunk_sound 419712 128 c419712))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 419840 128 c419840) (checkChunk_sound 419968 128 c419968)) (Checked.append (checkChunk_sound 420096 128 c420096) (checkChunk_sound 420224 128 c420224))) (Checked.append (Checked.append (checkChunk_sound 420352 128 c420352) (checkChunk_sound 420480 128 c420480)) (Checked.append (checkChunk_sound 420608 128 c420608) (checkChunk_sound 420736 128 c420736)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 420864 128 c420864) (checkChunk_sound 420992 128 c420992)) (Checked.append (checkChunk_sound 421120 128 c421120) (checkChunk_sound 421248 128 c421248))) (Checked.append (Checked.append (checkChunk_sound 421376 128 c421376) (checkChunk_sound 421504 128 c421504)) (Checked.append (checkChunk_sound 421632 128 c421632) (checkChunk_sound 421760 128 c421760)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 421888 128 c421888) (checkChunk_sound 422016 128 c422016)) (Checked.append (checkChunk_sound 422144 128 c422144) (checkChunk_sound 422272 128 c422272))) (Checked.append (Checked.append (checkChunk_sound 422400 128 c422400) (checkChunk_sound 422528 128 c422528)) (Checked.append (checkChunk_sound 422656 128 c422656) (checkChunk_sound 422784 128 c422784)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 422912 128 c422912) (checkChunk_sound 423040 128 c423040)) (Checked.append (checkChunk_sound 423168 128 c423168) (checkChunk_sound 423296 128 c423296))) (Checked.append (Checked.append (checkChunk_sound 423424 128 c423424) (checkChunk_sound 423552 128 c423552)) (Checked.append (checkChunk_sound 423680 128 c423680) (checkChunk_sound 423808 128 c423808))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 423936 128 c423936) (checkChunk_sound 424064 128 c424064)) (Checked.append (checkChunk_sound 424192 128 c424192) (checkChunk_sound 424320 128 c424320))) (Checked.append (Checked.append (checkChunk_sound 424448 128 c424448) (checkChunk_sound 424576 128 c424576)) (Checked.append (checkChunk_sound 424704 128 c424704) (checkChunk_sound 424832 128 c424832)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 424960 128 c424960) (checkChunk_sound 425088 128 c425088)) (Checked.append (checkChunk_sound 425216 128 c425216) (checkChunk_sound 425344 128 c425344))) (Checked.append (Checked.append (checkChunk_sound 425472 128 c425472) (checkChunk_sound 425600 128 c425600)) (Checked.append (checkChunk_sound 425728 128 c425728) (checkChunk_sound 425856 128 c425856)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B024
