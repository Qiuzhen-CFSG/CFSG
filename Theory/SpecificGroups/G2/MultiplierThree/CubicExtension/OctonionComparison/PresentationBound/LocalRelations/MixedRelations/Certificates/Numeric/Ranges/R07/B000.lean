module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1499136, 1507328).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B000
private theorem c1499136 : checkChunk 1499136 128 = true := by decide +kernel
private theorem c1499264 : checkChunk 1499264 128 = true := by decide +kernel
private theorem c1499392 : checkChunk 1499392 128 = true := by decide +kernel
private theorem c1499520 : checkChunk 1499520 128 = true := by decide +kernel
private theorem c1499648 : checkChunk 1499648 128 = true := by decide +kernel
private theorem c1499776 : checkChunk 1499776 128 = true := by decide +kernel
private theorem c1499904 : checkChunk 1499904 128 = true := by decide +kernel
private theorem c1500032 : checkChunk 1500032 128 = true := by decide +kernel
private theorem c1500160 : checkChunk 1500160 128 = true := by decide +kernel
private theorem c1500288 : checkChunk 1500288 128 = true := by decide +kernel
private theorem c1500416 : checkChunk 1500416 128 = true := by decide +kernel
private theorem c1500544 : checkChunk 1500544 128 = true := by decide +kernel
private theorem c1500672 : checkChunk 1500672 128 = true := by decide +kernel
private theorem c1500800 : checkChunk 1500800 128 = true := by decide +kernel
private theorem c1500928 : checkChunk 1500928 128 = true := by decide +kernel
private theorem c1501056 : checkChunk 1501056 128 = true := by decide +kernel
private theorem c1501184 : checkChunk 1501184 128 = true := by decide +kernel
private theorem c1501312 : checkChunk 1501312 128 = true := by decide +kernel
private theorem c1501440 : checkChunk 1501440 128 = true := by decide +kernel
private theorem c1501568 : checkChunk 1501568 128 = true := by decide +kernel
private theorem c1501696 : checkChunk 1501696 128 = true := by decide +kernel
private theorem c1501824 : checkChunk 1501824 128 = true := by decide +kernel
private theorem c1501952 : checkChunk 1501952 128 = true := by decide +kernel
private theorem c1502080 : checkChunk 1502080 128 = true := by decide +kernel
private theorem c1502208 : checkChunk 1502208 128 = true := by decide +kernel
private theorem c1502336 : checkChunk 1502336 128 = true := by decide +kernel
private theorem c1502464 : checkChunk 1502464 128 = true := by decide +kernel
private theorem c1502592 : checkChunk 1502592 128 = true := by decide +kernel
private theorem c1502720 : checkChunk 1502720 128 = true := by decide +kernel
private theorem c1502848 : checkChunk 1502848 128 = true := by decide +kernel
private theorem c1502976 : checkChunk 1502976 128 = true := by decide +kernel
private theorem c1503104 : checkChunk 1503104 128 = true := by decide +kernel
private theorem c1503232 : checkChunk 1503232 128 = true := by decide +kernel
private theorem c1503360 : checkChunk 1503360 128 = true := by decide +kernel
private theorem c1503488 : checkChunk 1503488 128 = true := by decide +kernel
private theorem c1503616 : checkChunk 1503616 128 = true := by decide +kernel
private theorem c1503744 : checkChunk 1503744 128 = true := by decide +kernel
private theorem c1503872 : checkChunk 1503872 128 = true := by decide +kernel
private theorem c1504000 : checkChunk 1504000 128 = true := by decide +kernel
private theorem c1504128 : checkChunk 1504128 128 = true := by decide +kernel
private theorem c1504256 : checkChunk 1504256 128 = true := by decide +kernel
private theorem c1504384 : checkChunk 1504384 128 = true := by decide +kernel
private theorem c1504512 : checkChunk 1504512 128 = true := by decide +kernel
private theorem c1504640 : checkChunk 1504640 128 = true := by decide +kernel
private theorem c1504768 : checkChunk 1504768 128 = true := by decide +kernel
private theorem c1504896 : checkChunk 1504896 128 = true := by decide +kernel
private theorem c1505024 : checkChunk 1505024 128 = true := by decide +kernel
private theorem c1505152 : checkChunk 1505152 128 = true := by decide +kernel
private theorem c1505280 : checkChunk 1505280 128 = true := by decide +kernel
private theorem c1505408 : checkChunk 1505408 128 = true := by decide +kernel
private theorem c1505536 : checkChunk 1505536 128 = true := by decide +kernel
private theorem c1505664 : checkChunk 1505664 128 = true := by decide +kernel
private theorem c1505792 : checkChunk 1505792 128 = true := by decide +kernel
private theorem c1505920 : checkChunk 1505920 128 = true := by decide +kernel
private theorem c1506048 : checkChunk 1506048 128 = true := by decide +kernel
private theorem c1506176 : checkChunk 1506176 128 = true := by decide +kernel
private theorem c1506304 : checkChunk 1506304 128 = true := by decide +kernel
private theorem c1506432 : checkChunk 1506432 128 = true := by decide +kernel
private theorem c1506560 : checkChunk 1506560 128 = true := by decide +kernel
private theorem c1506688 : checkChunk 1506688 128 = true := by decide +kernel
private theorem c1506816 : checkChunk 1506816 128 = true := by decide +kernel
private theorem c1506944 : checkChunk 1506944 128 = true := by decide +kernel
private theorem c1507072 : checkChunk 1507072 128 = true := by decide +kernel
private theorem c1507200 : checkChunk 1507200 128 = true := by decide +kernel

public theorem checked : Checked 1499136 1507328 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1499136 128 c1499136) (checkChunk_sound 1499264 128 c1499264)) (Checked.append (checkChunk_sound 1499392 128 c1499392) (checkChunk_sound 1499520 128 c1499520))) (Checked.append (Checked.append (checkChunk_sound 1499648 128 c1499648) (checkChunk_sound 1499776 128 c1499776)) (Checked.append (checkChunk_sound 1499904 128 c1499904) (checkChunk_sound 1500032 128 c1500032)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1500160 128 c1500160) (checkChunk_sound 1500288 128 c1500288)) (Checked.append (checkChunk_sound 1500416 128 c1500416) (checkChunk_sound 1500544 128 c1500544))) (Checked.append (Checked.append (checkChunk_sound 1500672 128 c1500672) (checkChunk_sound 1500800 128 c1500800)) (Checked.append (checkChunk_sound 1500928 128 c1500928) (checkChunk_sound 1501056 128 c1501056))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1501184 128 c1501184) (checkChunk_sound 1501312 128 c1501312)) (Checked.append (checkChunk_sound 1501440 128 c1501440) (checkChunk_sound 1501568 128 c1501568))) (Checked.append (Checked.append (checkChunk_sound 1501696 128 c1501696) (checkChunk_sound 1501824 128 c1501824)) (Checked.append (checkChunk_sound 1501952 128 c1501952) (checkChunk_sound 1502080 128 c1502080)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1502208 128 c1502208) (checkChunk_sound 1502336 128 c1502336)) (Checked.append (checkChunk_sound 1502464 128 c1502464) (checkChunk_sound 1502592 128 c1502592))) (Checked.append (Checked.append (checkChunk_sound 1502720 128 c1502720) (checkChunk_sound 1502848 128 c1502848)) (Checked.append (checkChunk_sound 1502976 128 c1502976) (checkChunk_sound 1503104 128 c1503104)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1503232 128 c1503232) (checkChunk_sound 1503360 128 c1503360)) (Checked.append (checkChunk_sound 1503488 128 c1503488) (checkChunk_sound 1503616 128 c1503616))) (Checked.append (Checked.append (checkChunk_sound 1503744 128 c1503744) (checkChunk_sound 1503872 128 c1503872)) (Checked.append (checkChunk_sound 1504000 128 c1504000) (checkChunk_sound 1504128 128 c1504128)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1504256 128 c1504256) (checkChunk_sound 1504384 128 c1504384)) (Checked.append (checkChunk_sound 1504512 128 c1504512) (checkChunk_sound 1504640 128 c1504640))) (Checked.append (Checked.append (checkChunk_sound 1504768 128 c1504768) (checkChunk_sound 1504896 128 c1504896)) (Checked.append (checkChunk_sound 1505024 128 c1505024) (checkChunk_sound 1505152 128 c1505152))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1505280 128 c1505280) (checkChunk_sound 1505408 128 c1505408)) (Checked.append (checkChunk_sound 1505536 128 c1505536) (checkChunk_sound 1505664 128 c1505664))) (Checked.append (Checked.append (checkChunk_sound 1505792 128 c1505792) (checkChunk_sound 1505920 128 c1505920)) (Checked.append (checkChunk_sound 1506048 128 c1506048) (checkChunk_sound 1506176 128 c1506176)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1506304 128 c1506304) (checkChunk_sound 1506432 128 c1506432)) (Checked.append (checkChunk_sound 1506560 128 c1506560) (checkChunk_sound 1506688 128 c1506688))) (Checked.append (Checked.append (checkChunk_sound 1506816 128 c1506816) (checkChunk_sound 1506944 128 c1506944)) (Checked.append (checkChunk_sound 1507072 128 c1507072) (checkChunk_sound 1507200 128 c1507200)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B000
