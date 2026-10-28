module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1376256, 1384448).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B011
private theorem c1376256 : checkChunk 1376256 128 = true := by decide +kernel
private theorem c1376384 : checkChunk 1376384 128 = true := by decide +kernel
private theorem c1376512 : checkChunk 1376512 128 = true := by decide +kernel
private theorem c1376640 : checkChunk 1376640 128 = true := by decide +kernel
private theorem c1376768 : checkChunk 1376768 128 = true := by decide +kernel
private theorem c1376896 : checkChunk 1376896 128 = true := by decide +kernel
private theorem c1377024 : checkChunk 1377024 128 = true := by decide +kernel
private theorem c1377152 : checkChunk 1377152 128 = true := by decide +kernel
private theorem c1377280 : checkChunk 1377280 128 = true := by decide +kernel
private theorem c1377408 : checkChunk 1377408 128 = true := by decide +kernel
private theorem c1377536 : checkChunk 1377536 128 = true := by decide +kernel
private theorem c1377664 : checkChunk 1377664 128 = true := by decide +kernel
private theorem c1377792 : checkChunk 1377792 128 = true := by decide +kernel
private theorem c1377920 : checkChunk 1377920 128 = true := by decide +kernel
private theorem c1378048 : checkChunk 1378048 128 = true := by decide +kernel
private theorem c1378176 : checkChunk 1378176 128 = true := by decide +kernel
private theorem c1378304 : checkChunk 1378304 128 = true := by decide +kernel
private theorem c1378432 : checkChunk 1378432 128 = true := by decide +kernel
private theorem c1378560 : checkChunk 1378560 128 = true := by decide +kernel
private theorem c1378688 : checkChunk 1378688 128 = true := by decide +kernel
private theorem c1378816 : checkChunk 1378816 128 = true := by decide +kernel
private theorem c1378944 : checkChunk 1378944 128 = true := by decide +kernel
private theorem c1379072 : checkChunk 1379072 128 = true := by decide +kernel
private theorem c1379200 : checkChunk 1379200 128 = true := by decide +kernel
private theorem c1379328 : checkChunk 1379328 128 = true := by decide +kernel
private theorem c1379456 : checkChunk 1379456 128 = true := by decide +kernel
private theorem c1379584 : checkChunk 1379584 128 = true := by decide +kernel
private theorem c1379712 : checkChunk 1379712 128 = true := by decide +kernel
private theorem c1379840 : checkChunk 1379840 128 = true := by decide +kernel
private theorem c1379968 : checkChunk 1379968 128 = true := by decide +kernel
private theorem c1380096 : checkChunk 1380096 128 = true := by decide +kernel
private theorem c1380224 : checkChunk 1380224 128 = true := by decide +kernel
private theorem c1380352 : checkChunk 1380352 128 = true := by decide +kernel
private theorem c1380480 : checkChunk 1380480 128 = true := by decide +kernel
private theorem c1380608 : checkChunk 1380608 128 = true := by decide +kernel
private theorem c1380736 : checkChunk 1380736 128 = true := by decide +kernel
private theorem c1380864 : checkChunk 1380864 128 = true := by decide +kernel
private theorem c1380992 : checkChunk 1380992 128 = true := by decide +kernel
private theorem c1381120 : checkChunk 1381120 128 = true := by decide +kernel
private theorem c1381248 : checkChunk 1381248 128 = true := by decide +kernel
private theorem c1381376 : checkChunk 1381376 128 = true := by decide +kernel
private theorem c1381504 : checkChunk 1381504 128 = true := by decide +kernel
private theorem c1381632 : checkChunk 1381632 128 = true := by decide +kernel
private theorem c1381760 : checkChunk 1381760 128 = true := by decide +kernel
private theorem c1381888 : checkChunk 1381888 128 = true := by decide +kernel
private theorem c1382016 : checkChunk 1382016 128 = true := by decide +kernel
private theorem c1382144 : checkChunk 1382144 128 = true := by decide +kernel
private theorem c1382272 : checkChunk 1382272 128 = true := by decide +kernel
private theorem c1382400 : checkChunk 1382400 128 = true := by decide +kernel
private theorem c1382528 : checkChunk 1382528 128 = true := by decide +kernel
private theorem c1382656 : checkChunk 1382656 128 = true := by decide +kernel
private theorem c1382784 : checkChunk 1382784 128 = true := by decide +kernel
private theorem c1382912 : checkChunk 1382912 128 = true := by decide +kernel
private theorem c1383040 : checkChunk 1383040 128 = true := by decide +kernel
private theorem c1383168 : checkChunk 1383168 128 = true := by decide +kernel
private theorem c1383296 : checkChunk 1383296 128 = true := by decide +kernel
private theorem c1383424 : checkChunk 1383424 128 = true := by decide +kernel
private theorem c1383552 : checkChunk 1383552 128 = true := by decide +kernel
private theorem c1383680 : checkChunk 1383680 128 = true := by decide +kernel
private theorem c1383808 : checkChunk 1383808 128 = true := by decide +kernel
private theorem c1383936 : checkChunk 1383936 128 = true := by decide +kernel
private theorem c1384064 : checkChunk 1384064 128 = true := by decide +kernel
private theorem c1384192 : checkChunk 1384192 128 = true := by decide +kernel
private theorem c1384320 : checkChunk 1384320 128 = true := by decide +kernel

public theorem checked : Checked 1376256 1384448 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1376256 128 c1376256) (checkChunk_sound 1376384 128 c1376384)) (Checked.append (checkChunk_sound 1376512 128 c1376512) (checkChunk_sound 1376640 128 c1376640))) (Checked.append (Checked.append (checkChunk_sound 1376768 128 c1376768) (checkChunk_sound 1376896 128 c1376896)) (Checked.append (checkChunk_sound 1377024 128 c1377024) (checkChunk_sound 1377152 128 c1377152)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1377280 128 c1377280) (checkChunk_sound 1377408 128 c1377408)) (Checked.append (checkChunk_sound 1377536 128 c1377536) (checkChunk_sound 1377664 128 c1377664))) (Checked.append (Checked.append (checkChunk_sound 1377792 128 c1377792) (checkChunk_sound 1377920 128 c1377920)) (Checked.append (checkChunk_sound 1378048 128 c1378048) (checkChunk_sound 1378176 128 c1378176))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1378304 128 c1378304) (checkChunk_sound 1378432 128 c1378432)) (Checked.append (checkChunk_sound 1378560 128 c1378560) (checkChunk_sound 1378688 128 c1378688))) (Checked.append (Checked.append (checkChunk_sound 1378816 128 c1378816) (checkChunk_sound 1378944 128 c1378944)) (Checked.append (checkChunk_sound 1379072 128 c1379072) (checkChunk_sound 1379200 128 c1379200)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1379328 128 c1379328) (checkChunk_sound 1379456 128 c1379456)) (Checked.append (checkChunk_sound 1379584 128 c1379584) (checkChunk_sound 1379712 128 c1379712))) (Checked.append (Checked.append (checkChunk_sound 1379840 128 c1379840) (checkChunk_sound 1379968 128 c1379968)) (Checked.append (checkChunk_sound 1380096 128 c1380096) (checkChunk_sound 1380224 128 c1380224)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1380352 128 c1380352) (checkChunk_sound 1380480 128 c1380480)) (Checked.append (checkChunk_sound 1380608 128 c1380608) (checkChunk_sound 1380736 128 c1380736))) (Checked.append (Checked.append (checkChunk_sound 1380864 128 c1380864) (checkChunk_sound 1380992 128 c1380992)) (Checked.append (checkChunk_sound 1381120 128 c1381120) (checkChunk_sound 1381248 128 c1381248)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1381376 128 c1381376) (checkChunk_sound 1381504 128 c1381504)) (Checked.append (checkChunk_sound 1381632 128 c1381632) (checkChunk_sound 1381760 128 c1381760))) (Checked.append (Checked.append (checkChunk_sound 1381888 128 c1381888) (checkChunk_sound 1382016 128 c1382016)) (Checked.append (checkChunk_sound 1382144 128 c1382144) (checkChunk_sound 1382272 128 c1382272))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1382400 128 c1382400) (checkChunk_sound 1382528 128 c1382528)) (Checked.append (checkChunk_sound 1382656 128 c1382656) (checkChunk_sound 1382784 128 c1382784))) (Checked.append (Checked.append (checkChunk_sound 1382912 128 c1382912) (checkChunk_sound 1383040 128 c1383040)) (Checked.append (checkChunk_sound 1383168 128 c1383168) (checkChunk_sound 1383296 128 c1383296)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1383424 128 c1383424) (checkChunk_sound 1383552 128 c1383552)) (Checked.append (checkChunk_sound 1383680 128 c1383680) (checkChunk_sound 1383808 128 c1383808))) (Checked.append (Checked.append (checkChunk_sound 1383936 128 c1383936) (checkChunk_sound 1384064 128 c1384064)) (Checked.append (checkChunk_sound 1384192 128 c1384192) (checkChunk_sound 1384320 128 c1384320)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B011
