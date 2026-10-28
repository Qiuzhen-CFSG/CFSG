module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1343488, 1351680).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B007
private theorem c1343488 : checkChunk 1343488 128 = true := by decide +kernel
private theorem c1343616 : checkChunk 1343616 128 = true := by decide +kernel
private theorem c1343744 : checkChunk 1343744 128 = true := by decide +kernel
private theorem c1343872 : checkChunk 1343872 128 = true := by decide +kernel
private theorem c1344000 : checkChunk 1344000 128 = true := by decide +kernel
private theorem c1344128 : checkChunk 1344128 128 = true := by decide +kernel
private theorem c1344256 : checkChunk 1344256 128 = true := by decide +kernel
private theorem c1344384 : checkChunk 1344384 128 = true := by decide +kernel
private theorem c1344512 : checkChunk 1344512 128 = true := by decide +kernel
private theorem c1344640 : checkChunk 1344640 128 = true := by decide +kernel
private theorem c1344768 : checkChunk 1344768 128 = true := by decide +kernel
private theorem c1344896 : checkChunk 1344896 128 = true := by decide +kernel
private theorem c1345024 : checkChunk 1345024 128 = true := by decide +kernel
private theorem c1345152 : checkChunk 1345152 128 = true := by decide +kernel
private theorem c1345280 : checkChunk 1345280 128 = true := by decide +kernel
private theorem c1345408 : checkChunk 1345408 128 = true := by decide +kernel
private theorem c1345536 : checkChunk 1345536 128 = true := by decide +kernel
private theorem c1345664 : checkChunk 1345664 128 = true := by decide +kernel
private theorem c1345792 : checkChunk 1345792 128 = true := by decide +kernel
private theorem c1345920 : checkChunk 1345920 128 = true := by decide +kernel
private theorem c1346048 : checkChunk 1346048 128 = true := by decide +kernel
private theorem c1346176 : checkChunk 1346176 128 = true := by decide +kernel
private theorem c1346304 : checkChunk 1346304 128 = true := by decide +kernel
private theorem c1346432 : checkChunk 1346432 128 = true := by decide +kernel
private theorem c1346560 : checkChunk 1346560 128 = true := by decide +kernel
private theorem c1346688 : checkChunk 1346688 128 = true := by decide +kernel
private theorem c1346816 : checkChunk 1346816 128 = true := by decide +kernel
private theorem c1346944 : checkChunk 1346944 128 = true := by decide +kernel
private theorem c1347072 : checkChunk 1347072 128 = true := by decide +kernel
private theorem c1347200 : checkChunk 1347200 128 = true := by decide +kernel
private theorem c1347328 : checkChunk 1347328 128 = true := by decide +kernel
private theorem c1347456 : checkChunk 1347456 128 = true := by decide +kernel
private theorem c1347584 : checkChunk 1347584 128 = true := by decide +kernel
private theorem c1347712 : checkChunk 1347712 128 = true := by decide +kernel
private theorem c1347840 : checkChunk 1347840 128 = true := by decide +kernel
private theorem c1347968 : checkChunk 1347968 128 = true := by decide +kernel
private theorem c1348096 : checkChunk 1348096 128 = true := by decide +kernel
private theorem c1348224 : checkChunk 1348224 128 = true := by decide +kernel
private theorem c1348352 : checkChunk 1348352 128 = true := by decide +kernel
private theorem c1348480 : checkChunk 1348480 128 = true := by decide +kernel
private theorem c1348608 : checkChunk 1348608 128 = true := by decide +kernel
private theorem c1348736 : checkChunk 1348736 128 = true := by decide +kernel
private theorem c1348864 : checkChunk 1348864 128 = true := by decide +kernel
private theorem c1348992 : checkChunk 1348992 128 = true := by decide +kernel
private theorem c1349120 : checkChunk 1349120 128 = true := by decide +kernel
private theorem c1349248 : checkChunk 1349248 128 = true := by decide +kernel
private theorem c1349376 : checkChunk 1349376 128 = true := by decide +kernel
private theorem c1349504 : checkChunk 1349504 128 = true := by decide +kernel
private theorem c1349632 : checkChunk 1349632 128 = true := by decide +kernel
private theorem c1349760 : checkChunk 1349760 128 = true := by decide +kernel
private theorem c1349888 : checkChunk 1349888 128 = true := by decide +kernel
private theorem c1350016 : checkChunk 1350016 128 = true := by decide +kernel
private theorem c1350144 : checkChunk 1350144 128 = true := by decide +kernel
private theorem c1350272 : checkChunk 1350272 128 = true := by decide +kernel
private theorem c1350400 : checkChunk 1350400 128 = true := by decide +kernel
private theorem c1350528 : checkChunk 1350528 128 = true := by decide +kernel
private theorem c1350656 : checkChunk 1350656 128 = true := by decide +kernel
private theorem c1350784 : checkChunk 1350784 128 = true := by decide +kernel
private theorem c1350912 : checkChunk 1350912 128 = true := by decide +kernel
private theorem c1351040 : checkChunk 1351040 128 = true := by decide +kernel
private theorem c1351168 : checkChunk 1351168 128 = true := by decide +kernel
private theorem c1351296 : checkChunk 1351296 128 = true := by decide +kernel
private theorem c1351424 : checkChunk 1351424 128 = true := by decide +kernel
private theorem c1351552 : checkChunk 1351552 128 = true := by decide +kernel

public theorem checked : Checked 1343488 1351680 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1343488 128 c1343488) (checkChunk_sound 1343616 128 c1343616)) (Checked.append (checkChunk_sound 1343744 128 c1343744) (checkChunk_sound 1343872 128 c1343872))) (Checked.append (Checked.append (checkChunk_sound 1344000 128 c1344000) (checkChunk_sound 1344128 128 c1344128)) (Checked.append (checkChunk_sound 1344256 128 c1344256) (checkChunk_sound 1344384 128 c1344384)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1344512 128 c1344512) (checkChunk_sound 1344640 128 c1344640)) (Checked.append (checkChunk_sound 1344768 128 c1344768) (checkChunk_sound 1344896 128 c1344896))) (Checked.append (Checked.append (checkChunk_sound 1345024 128 c1345024) (checkChunk_sound 1345152 128 c1345152)) (Checked.append (checkChunk_sound 1345280 128 c1345280) (checkChunk_sound 1345408 128 c1345408))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1345536 128 c1345536) (checkChunk_sound 1345664 128 c1345664)) (Checked.append (checkChunk_sound 1345792 128 c1345792) (checkChunk_sound 1345920 128 c1345920))) (Checked.append (Checked.append (checkChunk_sound 1346048 128 c1346048) (checkChunk_sound 1346176 128 c1346176)) (Checked.append (checkChunk_sound 1346304 128 c1346304) (checkChunk_sound 1346432 128 c1346432)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1346560 128 c1346560) (checkChunk_sound 1346688 128 c1346688)) (Checked.append (checkChunk_sound 1346816 128 c1346816) (checkChunk_sound 1346944 128 c1346944))) (Checked.append (Checked.append (checkChunk_sound 1347072 128 c1347072) (checkChunk_sound 1347200 128 c1347200)) (Checked.append (checkChunk_sound 1347328 128 c1347328) (checkChunk_sound 1347456 128 c1347456)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1347584 128 c1347584) (checkChunk_sound 1347712 128 c1347712)) (Checked.append (checkChunk_sound 1347840 128 c1347840) (checkChunk_sound 1347968 128 c1347968))) (Checked.append (Checked.append (checkChunk_sound 1348096 128 c1348096) (checkChunk_sound 1348224 128 c1348224)) (Checked.append (checkChunk_sound 1348352 128 c1348352) (checkChunk_sound 1348480 128 c1348480)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1348608 128 c1348608) (checkChunk_sound 1348736 128 c1348736)) (Checked.append (checkChunk_sound 1348864 128 c1348864) (checkChunk_sound 1348992 128 c1348992))) (Checked.append (Checked.append (checkChunk_sound 1349120 128 c1349120) (checkChunk_sound 1349248 128 c1349248)) (Checked.append (checkChunk_sound 1349376 128 c1349376) (checkChunk_sound 1349504 128 c1349504))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1349632 128 c1349632) (checkChunk_sound 1349760 128 c1349760)) (Checked.append (checkChunk_sound 1349888 128 c1349888) (checkChunk_sound 1350016 128 c1350016))) (Checked.append (Checked.append (checkChunk_sound 1350144 128 c1350144) (checkChunk_sound 1350272 128 c1350272)) (Checked.append (checkChunk_sound 1350400 128 c1350400) (checkChunk_sound 1350528 128 c1350528)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1350656 128 c1350656) (checkChunk_sound 1350784 128 c1350784)) (Checked.append (checkChunk_sound 1350912 128 c1350912) (checkChunk_sound 1351040 128 c1351040))) (Checked.append (Checked.append (checkChunk_sound 1351168 128 c1351168) (checkChunk_sound 1351296 128 c1351296)) (Checked.append (checkChunk_sound 1351424 128 c1351424) (checkChunk_sound 1351552 128 c1351552)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B007
