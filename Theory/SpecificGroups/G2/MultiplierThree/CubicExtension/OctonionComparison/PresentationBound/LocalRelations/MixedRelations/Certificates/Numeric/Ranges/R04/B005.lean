module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [901120, 909312).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B005
private theorem c901120 : checkChunk 901120 128 = true := by decide +kernel
private theorem c901248 : checkChunk 901248 128 = true := by decide +kernel
private theorem c901376 : checkChunk 901376 128 = true := by decide +kernel
private theorem c901504 : checkChunk 901504 128 = true := by decide +kernel
private theorem c901632 : checkChunk 901632 128 = true := by decide +kernel
private theorem c901760 : checkChunk 901760 128 = true := by decide +kernel
private theorem c901888 : checkChunk 901888 128 = true := by decide +kernel
private theorem c902016 : checkChunk 902016 128 = true := by decide +kernel
private theorem c902144 : checkChunk 902144 128 = true := by decide +kernel
private theorem c902272 : checkChunk 902272 128 = true := by decide +kernel
private theorem c902400 : checkChunk 902400 128 = true := by decide +kernel
private theorem c902528 : checkChunk 902528 128 = true := by decide +kernel
private theorem c902656 : checkChunk 902656 128 = true := by decide +kernel
private theorem c902784 : checkChunk 902784 128 = true := by decide +kernel
private theorem c902912 : checkChunk 902912 128 = true := by decide +kernel
private theorem c903040 : checkChunk 903040 128 = true := by decide +kernel
private theorem c903168 : checkChunk 903168 128 = true := by decide +kernel
private theorem c903296 : checkChunk 903296 128 = true := by decide +kernel
private theorem c903424 : checkChunk 903424 128 = true := by decide +kernel
private theorem c903552 : checkChunk 903552 128 = true := by decide +kernel
private theorem c903680 : checkChunk 903680 128 = true := by decide +kernel
private theorem c903808 : checkChunk 903808 128 = true := by decide +kernel
private theorem c903936 : checkChunk 903936 128 = true := by decide +kernel
private theorem c904064 : checkChunk 904064 128 = true := by decide +kernel
private theorem c904192 : checkChunk 904192 128 = true := by decide +kernel
private theorem c904320 : checkChunk 904320 128 = true := by decide +kernel
private theorem c904448 : checkChunk 904448 128 = true := by decide +kernel
private theorem c904576 : checkChunk 904576 128 = true := by decide +kernel
private theorem c904704 : checkChunk 904704 128 = true := by decide +kernel
private theorem c904832 : checkChunk 904832 128 = true := by decide +kernel
private theorem c904960 : checkChunk 904960 128 = true := by decide +kernel
private theorem c905088 : checkChunk 905088 128 = true := by decide +kernel
private theorem c905216 : checkChunk 905216 128 = true := by decide +kernel
private theorem c905344 : checkChunk 905344 128 = true := by decide +kernel
private theorem c905472 : checkChunk 905472 128 = true := by decide +kernel
private theorem c905600 : checkChunk 905600 128 = true := by decide +kernel
private theorem c905728 : checkChunk 905728 128 = true := by decide +kernel
private theorem c905856 : checkChunk 905856 128 = true := by decide +kernel
private theorem c905984 : checkChunk 905984 128 = true := by decide +kernel
private theorem c906112 : checkChunk 906112 128 = true := by decide +kernel
private theorem c906240 : checkChunk 906240 128 = true := by decide +kernel
private theorem c906368 : checkChunk 906368 128 = true := by decide +kernel
private theorem c906496 : checkChunk 906496 128 = true := by decide +kernel
private theorem c906624 : checkChunk 906624 128 = true := by decide +kernel
private theorem c906752 : checkChunk 906752 128 = true := by decide +kernel
private theorem c906880 : checkChunk 906880 128 = true := by decide +kernel
private theorem c907008 : checkChunk 907008 128 = true := by decide +kernel
private theorem c907136 : checkChunk 907136 128 = true := by decide +kernel
private theorem c907264 : checkChunk 907264 128 = true := by decide +kernel
private theorem c907392 : checkChunk 907392 128 = true := by decide +kernel
private theorem c907520 : checkChunk 907520 128 = true := by decide +kernel
private theorem c907648 : checkChunk 907648 128 = true := by decide +kernel
private theorem c907776 : checkChunk 907776 128 = true := by decide +kernel
private theorem c907904 : checkChunk 907904 128 = true := by decide +kernel
private theorem c908032 : checkChunk 908032 128 = true := by decide +kernel
private theorem c908160 : checkChunk 908160 128 = true := by decide +kernel
private theorem c908288 : checkChunk 908288 128 = true := by decide +kernel
private theorem c908416 : checkChunk 908416 128 = true := by decide +kernel
private theorem c908544 : checkChunk 908544 128 = true := by decide +kernel
private theorem c908672 : checkChunk 908672 128 = true := by decide +kernel
private theorem c908800 : checkChunk 908800 128 = true := by decide +kernel
private theorem c908928 : checkChunk 908928 128 = true := by decide +kernel
private theorem c909056 : checkChunk 909056 128 = true := by decide +kernel
private theorem c909184 : checkChunk 909184 128 = true := by decide +kernel

public theorem checked : Checked 901120 909312 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 901120 128 c901120) (checkChunk_sound 901248 128 c901248)) (Checked.append (checkChunk_sound 901376 128 c901376) (checkChunk_sound 901504 128 c901504))) (Checked.append (Checked.append (checkChunk_sound 901632 128 c901632) (checkChunk_sound 901760 128 c901760)) (Checked.append (checkChunk_sound 901888 128 c901888) (checkChunk_sound 902016 128 c902016)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 902144 128 c902144) (checkChunk_sound 902272 128 c902272)) (Checked.append (checkChunk_sound 902400 128 c902400) (checkChunk_sound 902528 128 c902528))) (Checked.append (Checked.append (checkChunk_sound 902656 128 c902656) (checkChunk_sound 902784 128 c902784)) (Checked.append (checkChunk_sound 902912 128 c902912) (checkChunk_sound 903040 128 c903040))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 903168 128 c903168) (checkChunk_sound 903296 128 c903296)) (Checked.append (checkChunk_sound 903424 128 c903424) (checkChunk_sound 903552 128 c903552))) (Checked.append (Checked.append (checkChunk_sound 903680 128 c903680) (checkChunk_sound 903808 128 c903808)) (Checked.append (checkChunk_sound 903936 128 c903936) (checkChunk_sound 904064 128 c904064)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 904192 128 c904192) (checkChunk_sound 904320 128 c904320)) (Checked.append (checkChunk_sound 904448 128 c904448) (checkChunk_sound 904576 128 c904576))) (Checked.append (Checked.append (checkChunk_sound 904704 128 c904704) (checkChunk_sound 904832 128 c904832)) (Checked.append (checkChunk_sound 904960 128 c904960) (checkChunk_sound 905088 128 c905088)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 905216 128 c905216) (checkChunk_sound 905344 128 c905344)) (Checked.append (checkChunk_sound 905472 128 c905472) (checkChunk_sound 905600 128 c905600))) (Checked.append (Checked.append (checkChunk_sound 905728 128 c905728) (checkChunk_sound 905856 128 c905856)) (Checked.append (checkChunk_sound 905984 128 c905984) (checkChunk_sound 906112 128 c906112)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 906240 128 c906240) (checkChunk_sound 906368 128 c906368)) (Checked.append (checkChunk_sound 906496 128 c906496) (checkChunk_sound 906624 128 c906624))) (Checked.append (Checked.append (checkChunk_sound 906752 128 c906752) (checkChunk_sound 906880 128 c906880)) (Checked.append (checkChunk_sound 907008 128 c907008) (checkChunk_sound 907136 128 c907136))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 907264 128 c907264) (checkChunk_sound 907392 128 c907392)) (Checked.append (checkChunk_sound 907520 128 c907520) (checkChunk_sound 907648 128 c907648))) (Checked.append (Checked.append (checkChunk_sound 907776 128 c907776) (checkChunk_sound 907904 128 c907904)) (Checked.append (checkChunk_sound 908032 128 c908032) (checkChunk_sound 908160 128 c908160)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 908288 128 c908288) (checkChunk_sound 908416 128 c908416)) (Checked.append (checkChunk_sound 908544 128 c908544) (checkChunk_sound 908672 128 c908672))) (Checked.append (Checked.append (checkChunk_sound 908800 128 c908800) (checkChunk_sound 908928 128 c908928)) (Checked.append (checkChunk_sound 909056 128 c909056) (checkChunk_sound 909184 128 c909184)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B005
