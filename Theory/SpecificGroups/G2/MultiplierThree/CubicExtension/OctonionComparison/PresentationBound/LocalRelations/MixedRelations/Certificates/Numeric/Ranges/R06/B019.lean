module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1441792, 1449984).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B019
private theorem c1441792 : checkChunk 1441792 128 = true := by decide +kernel
private theorem c1441920 : checkChunk 1441920 128 = true := by decide +kernel
private theorem c1442048 : checkChunk 1442048 128 = true := by decide +kernel
private theorem c1442176 : checkChunk 1442176 128 = true := by decide +kernel
private theorem c1442304 : checkChunk 1442304 128 = true := by decide +kernel
private theorem c1442432 : checkChunk 1442432 128 = true := by decide +kernel
private theorem c1442560 : checkChunk 1442560 128 = true := by decide +kernel
private theorem c1442688 : checkChunk 1442688 128 = true := by decide +kernel
private theorem c1442816 : checkChunk 1442816 128 = true := by decide +kernel
private theorem c1442944 : checkChunk 1442944 128 = true := by decide +kernel
private theorem c1443072 : checkChunk 1443072 128 = true := by decide +kernel
private theorem c1443200 : checkChunk 1443200 128 = true := by decide +kernel
private theorem c1443328 : checkChunk 1443328 128 = true := by decide +kernel
private theorem c1443456 : checkChunk 1443456 128 = true := by decide +kernel
private theorem c1443584 : checkChunk 1443584 128 = true := by decide +kernel
private theorem c1443712 : checkChunk 1443712 128 = true := by decide +kernel
private theorem c1443840 : checkChunk 1443840 128 = true := by decide +kernel
private theorem c1443968 : checkChunk 1443968 128 = true := by decide +kernel
private theorem c1444096 : checkChunk 1444096 128 = true := by decide +kernel
private theorem c1444224 : checkChunk 1444224 128 = true := by decide +kernel
private theorem c1444352 : checkChunk 1444352 128 = true := by decide +kernel
private theorem c1444480 : checkChunk 1444480 128 = true := by decide +kernel
private theorem c1444608 : checkChunk 1444608 128 = true := by decide +kernel
private theorem c1444736 : checkChunk 1444736 128 = true := by decide +kernel
private theorem c1444864 : checkChunk 1444864 128 = true := by decide +kernel
private theorem c1444992 : checkChunk 1444992 128 = true := by decide +kernel
private theorem c1445120 : checkChunk 1445120 128 = true := by decide +kernel
private theorem c1445248 : checkChunk 1445248 128 = true := by decide +kernel
private theorem c1445376 : checkChunk 1445376 128 = true := by decide +kernel
private theorem c1445504 : checkChunk 1445504 128 = true := by decide +kernel
private theorem c1445632 : checkChunk 1445632 128 = true := by decide +kernel
private theorem c1445760 : checkChunk 1445760 128 = true := by decide +kernel
private theorem c1445888 : checkChunk 1445888 128 = true := by decide +kernel
private theorem c1446016 : checkChunk 1446016 128 = true := by decide +kernel
private theorem c1446144 : checkChunk 1446144 128 = true := by decide +kernel
private theorem c1446272 : checkChunk 1446272 128 = true := by decide +kernel
private theorem c1446400 : checkChunk 1446400 128 = true := by decide +kernel
private theorem c1446528 : checkChunk 1446528 128 = true := by decide +kernel
private theorem c1446656 : checkChunk 1446656 128 = true := by decide +kernel
private theorem c1446784 : checkChunk 1446784 128 = true := by decide +kernel
private theorem c1446912 : checkChunk 1446912 128 = true := by decide +kernel
private theorem c1447040 : checkChunk 1447040 128 = true := by decide +kernel
private theorem c1447168 : checkChunk 1447168 128 = true := by decide +kernel
private theorem c1447296 : checkChunk 1447296 128 = true := by decide +kernel
private theorem c1447424 : checkChunk 1447424 128 = true := by decide +kernel
private theorem c1447552 : checkChunk 1447552 128 = true := by decide +kernel
private theorem c1447680 : checkChunk 1447680 128 = true := by decide +kernel
private theorem c1447808 : checkChunk 1447808 128 = true := by decide +kernel
private theorem c1447936 : checkChunk 1447936 128 = true := by decide +kernel
private theorem c1448064 : checkChunk 1448064 128 = true := by decide +kernel
private theorem c1448192 : checkChunk 1448192 128 = true := by decide +kernel
private theorem c1448320 : checkChunk 1448320 128 = true := by decide +kernel
private theorem c1448448 : checkChunk 1448448 128 = true := by decide +kernel
private theorem c1448576 : checkChunk 1448576 128 = true := by decide +kernel
private theorem c1448704 : checkChunk 1448704 128 = true := by decide +kernel
private theorem c1448832 : checkChunk 1448832 128 = true := by decide +kernel
private theorem c1448960 : checkChunk 1448960 128 = true := by decide +kernel
private theorem c1449088 : checkChunk 1449088 128 = true := by decide +kernel
private theorem c1449216 : checkChunk 1449216 128 = true := by decide +kernel
private theorem c1449344 : checkChunk 1449344 128 = true := by decide +kernel
private theorem c1449472 : checkChunk 1449472 128 = true := by decide +kernel
private theorem c1449600 : checkChunk 1449600 128 = true := by decide +kernel
private theorem c1449728 : checkChunk 1449728 128 = true := by decide +kernel
private theorem c1449856 : checkChunk 1449856 128 = true := by decide +kernel

public theorem checked : Checked 1441792 1449984 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1441792 128 c1441792) (checkChunk_sound 1441920 128 c1441920)) (Checked.append (checkChunk_sound 1442048 128 c1442048) (checkChunk_sound 1442176 128 c1442176))) (Checked.append (Checked.append (checkChunk_sound 1442304 128 c1442304) (checkChunk_sound 1442432 128 c1442432)) (Checked.append (checkChunk_sound 1442560 128 c1442560) (checkChunk_sound 1442688 128 c1442688)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1442816 128 c1442816) (checkChunk_sound 1442944 128 c1442944)) (Checked.append (checkChunk_sound 1443072 128 c1443072) (checkChunk_sound 1443200 128 c1443200))) (Checked.append (Checked.append (checkChunk_sound 1443328 128 c1443328) (checkChunk_sound 1443456 128 c1443456)) (Checked.append (checkChunk_sound 1443584 128 c1443584) (checkChunk_sound 1443712 128 c1443712))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1443840 128 c1443840) (checkChunk_sound 1443968 128 c1443968)) (Checked.append (checkChunk_sound 1444096 128 c1444096) (checkChunk_sound 1444224 128 c1444224))) (Checked.append (Checked.append (checkChunk_sound 1444352 128 c1444352) (checkChunk_sound 1444480 128 c1444480)) (Checked.append (checkChunk_sound 1444608 128 c1444608) (checkChunk_sound 1444736 128 c1444736)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1444864 128 c1444864) (checkChunk_sound 1444992 128 c1444992)) (Checked.append (checkChunk_sound 1445120 128 c1445120) (checkChunk_sound 1445248 128 c1445248))) (Checked.append (Checked.append (checkChunk_sound 1445376 128 c1445376) (checkChunk_sound 1445504 128 c1445504)) (Checked.append (checkChunk_sound 1445632 128 c1445632) (checkChunk_sound 1445760 128 c1445760)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1445888 128 c1445888) (checkChunk_sound 1446016 128 c1446016)) (Checked.append (checkChunk_sound 1446144 128 c1446144) (checkChunk_sound 1446272 128 c1446272))) (Checked.append (Checked.append (checkChunk_sound 1446400 128 c1446400) (checkChunk_sound 1446528 128 c1446528)) (Checked.append (checkChunk_sound 1446656 128 c1446656) (checkChunk_sound 1446784 128 c1446784)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1446912 128 c1446912) (checkChunk_sound 1447040 128 c1447040)) (Checked.append (checkChunk_sound 1447168 128 c1447168) (checkChunk_sound 1447296 128 c1447296))) (Checked.append (Checked.append (checkChunk_sound 1447424 128 c1447424) (checkChunk_sound 1447552 128 c1447552)) (Checked.append (checkChunk_sound 1447680 128 c1447680) (checkChunk_sound 1447808 128 c1447808))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1447936 128 c1447936) (checkChunk_sound 1448064 128 c1448064)) (Checked.append (checkChunk_sound 1448192 128 c1448192) (checkChunk_sound 1448320 128 c1448320))) (Checked.append (Checked.append (checkChunk_sound 1448448 128 c1448448) (checkChunk_sound 1448576 128 c1448576)) (Checked.append (checkChunk_sound 1448704 128 c1448704) (checkChunk_sound 1448832 128 c1448832)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1448960 128 c1448960) (checkChunk_sound 1449088 128 c1449088)) (Checked.append (checkChunk_sound 1449216 128 c1449216) (checkChunk_sound 1449344 128 c1449344))) (Checked.append (Checked.append (checkChunk_sound 1449472 128 c1449472) (checkChunk_sound 1449600 128 c1449600)) (Checked.append (checkChunk_sound 1449728 128 c1449728) (checkChunk_sound 1449856 128 c1449856)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B019
