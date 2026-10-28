module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1392640, 1400832).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B013
private theorem c1392640 : checkChunk 1392640 128 = true := by decide +kernel
private theorem c1392768 : checkChunk 1392768 128 = true := by decide +kernel
private theorem c1392896 : checkChunk 1392896 128 = true := by decide +kernel
private theorem c1393024 : checkChunk 1393024 128 = true := by decide +kernel
private theorem c1393152 : checkChunk 1393152 128 = true := by decide +kernel
private theorem c1393280 : checkChunk 1393280 128 = true := by decide +kernel
private theorem c1393408 : checkChunk 1393408 128 = true := by decide +kernel
private theorem c1393536 : checkChunk 1393536 128 = true := by decide +kernel
private theorem c1393664 : checkChunk 1393664 128 = true := by decide +kernel
private theorem c1393792 : checkChunk 1393792 128 = true := by decide +kernel
private theorem c1393920 : checkChunk 1393920 128 = true := by decide +kernel
private theorem c1394048 : checkChunk 1394048 128 = true := by decide +kernel
private theorem c1394176 : checkChunk 1394176 128 = true := by decide +kernel
private theorem c1394304 : checkChunk 1394304 128 = true := by decide +kernel
private theorem c1394432 : checkChunk 1394432 128 = true := by decide +kernel
private theorem c1394560 : checkChunk 1394560 128 = true := by decide +kernel
private theorem c1394688 : checkChunk 1394688 128 = true := by decide +kernel
private theorem c1394816 : checkChunk 1394816 128 = true := by decide +kernel
private theorem c1394944 : checkChunk 1394944 128 = true := by decide +kernel
private theorem c1395072 : checkChunk 1395072 128 = true := by decide +kernel
private theorem c1395200 : checkChunk 1395200 128 = true := by decide +kernel
private theorem c1395328 : checkChunk 1395328 128 = true := by decide +kernel
private theorem c1395456 : checkChunk 1395456 128 = true := by decide +kernel
private theorem c1395584 : checkChunk 1395584 128 = true := by decide +kernel
private theorem c1395712 : checkChunk 1395712 128 = true := by decide +kernel
private theorem c1395840 : checkChunk 1395840 128 = true := by decide +kernel
private theorem c1395968 : checkChunk 1395968 128 = true := by decide +kernel
private theorem c1396096 : checkChunk 1396096 128 = true := by decide +kernel
private theorem c1396224 : checkChunk 1396224 128 = true := by decide +kernel
private theorem c1396352 : checkChunk 1396352 128 = true := by decide +kernel
private theorem c1396480 : checkChunk 1396480 128 = true := by decide +kernel
private theorem c1396608 : checkChunk 1396608 128 = true := by decide +kernel
private theorem c1396736 : checkChunk 1396736 128 = true := by decide +kernel
private theorem c1396864 : checkChunk 1396864 128 = true := by decide +kernel
private theorem c1396992 : checkChunk 1396992 128 = true := by decide +kernel
private theorem c1397120 : checkChunk 1397120 128 = true := by decide +kernel
private theorem c1397248 : checkChunk 1397248 128 = true := by decide +kernel
private theorem c1397376 : checkChunk 1397376 128 = true := by decide +kernel
private theorem c1397504 : checkChunk 1397504 128 = true := by decide +kernel
private theorem c1397632 : checkChunk 1397632 128 = true := by decide +kernel
private theorem c1397760 : checkChunk 1397760 128 = true := by decide +kernel
private theorem c1397888 : checkChunk 1397888 128 = true := by decide +kernel
private theorem c1398016 : checkChunk 1398016 128 = true := by decide +kernel
private theorem c1398144 : checkChunk 1398144 128 = true := by decide +kernel
private theorem c1398272 : checkChunk 1398272 128 = true := by decide +kernel
private theorem c1398400 : checkChunk 1398400 128 = true := by decide +kernel
private theorem c1398528 : checkChunk 1398528 128 = true := by decide +kernel
private theorem c1398656 : checkChunk 1398656 128 = true := by decide +kernel
private theorem c1398784 : checkChunk 1398784 128 = true := by decide +kernel
private theorem c1398912 : checkChunk 1398912 128 = true := by decide +kernel
private theorem c1399040 : checkChunk 1399040 128 = true := by decide +kernel
private theorem c1399168 : checkChunk 1399168 128 = true := by decide +kernel
private theorem c1399296 : checkChunk 1399296 128 = true := by decide +kernel
private theorem c1399424 : checkChunk 1399424 128 = true := by decide +kernel
private theorem c1399552 : checkChunk 1399552 128 = true := by decide +kernel
private theorem c1399680 : checkChunk 1399680 128 = true := by decide +kernel
private theorem c1399808 : checkChunk 1399808 128 = true := by decide +kernel
private theorem c1399936 : checkChunk 1399936 128 = true := by decide +kernel
private theorem c1400064 : checkChunk 1400064 128 = true := by decide +kernel
private theorem c1400192 : checkChunk 1400192 128 = true := by decide +kernel
private theorem c1400320 : checkChunk 1400320 128 = true := by decide +kernel
private theorem c1400448 : checkChunk 1400448 128 = true := by decide +kernel
private theorem c1400576 : checkChunk 1400576 128 = true := by decide +kernel
private theorem c1400704 : checkChunk 1400704 128 = true := by decide +kernel

public theorem checked : Checked 1392640 1400832 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1392640 128 c1392640) (checkChunk_sound 1392768 128 c1392768)) (Checked.append (checkChunk_sound 1392896 128 c1392896) (checkChunk_sound 1393024 128 c1393024))) (Checked.append (Checked.append (checkChunk_sound 1393152 128 c1393152) (checkChunk_sound 1393280 128 c1393280)) (Checked.append (checkChunk_sound 1393408 128 c1393408) (checkChunk_sound 1393536 128 c1393536)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1393664 128 c1393664) (checkChunk_sound 1393792 128 c1393792)) (Checked.append (checkChunk_sound 1393920 128 c1393920) (checkChunk_sound 1394048 128 c1394048))) (Checked.append (Checked.append (checkChunk_sound 1394176 128 c1394176) (checkChunk_sound 1394304 128 c1394304)) (Checked.append (checkChunk_sound 1394432 128 c1394432) (checkChunk_sound 1394560 128 c1394560))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1394688 128 c1394688) (checkChunk_sound 1394816 128 c1394816)) (Checked.append (checkChunk_sound 1394944 128 c1394944) (checkChunk_sound 1395072 128 c1395072))) (Checked.append (Checked.append (checkChunk_sound 1395200 128 c1395200) (checkChunk_sound 1395328 128 c1395328)) (Checked.append (checkChunk_sound 1395456 128 c1395456) (checkChunk_sound 1395584 128 c1395584)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1395712 128 c1395712) (checkChunk_sound 1395840 128 c1395840)) (Checked.append (checkChunk_sound 1395968 128 c1395968) (checkChunk_sound 1396096 128 c1396096))) (Checked.append (Checked.append (checkChunk_sound 1396224 128 c1396224) (checkChunk_sound 1396352 128 c1396352)) (Checked.append (checkChunk_sound 1396480 128 c1396480) (checkChunk_sound 1396608 128 c1396608)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1396736 128 c1396736) (checkChunk_sound 1396864 128 c1396864)) (Checked.append (checkChunk_sound 1396992 128 c1396992) (checkChunk_sound 1397120 128 c1397120))) (Checked.append (Checked.append (checkChunk_sound 1397248 128 c1397248) (checkChunk_sound 1397376 128 c1397376)) (Checked.append (checkChunk_sound 1397504 128 c1397504) (checkChunk_sound 1397632 128 c1397632)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1397760 128 c1397760) (checkChunk_sound 1397888 128 c1397888)) (Checked.append (checkChunk_sound 1398016 128 c1398016) (checkChunk_sound 1398144 128 c1398144))) (Checked.append (Checked.append (checkChunk_sound 1398272 128 c1398272) (checkChunk_sound 1398400 128 c1398400)) (Checked.append (checkChunk_sound 1398528 128 c1398528) (checkChunk_sound 1398656 128 c1398656))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1398784 128 c1398784) (checkChunk_sound 1398912 128 c1398912)) (Checked.append (checkChunk_sound 1399040 128 c1399040) (checkChunk_sound 1399168 128 c1399168))) (Checked.append (Checked.append (checkChunk_sound 1399296 128 c1399296) (checkChunk_sound 1399424 128 c1399424)) (Checked.append (checkChunk_sound 1399552 128 c1399552) (checkChunk_sound 1399680 128 c1399680)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1399808 128 c1399808) (checkChunk_sound 1399936 128 c1399936)) (Checked.append (checkChunk_sound 1400064 128 c1400064) (checkChunk_sound 1400192 128 c1400192))) (Checked.append (Checked.append (checkChunk_sound 1400320 128 c1400320) (checkChunk_sound 1400448 128 c1400448)) (Checked.append (checkChunk_sound 1400576 128 c1400576) (checkChunk_sound 1400704 128 c1400704)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B013
