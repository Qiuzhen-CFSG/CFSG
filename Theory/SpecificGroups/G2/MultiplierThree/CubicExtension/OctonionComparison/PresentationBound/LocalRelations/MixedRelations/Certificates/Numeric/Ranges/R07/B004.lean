module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1531904, 1540096).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B004
private theorem c1531904 : checkChunk 1531904 128 = true := by decide +kernel
private theorem c1532032 : checkChunk 1532032 128 = true := by decide +kernel
private theorem c1532160 : checkChunk 1532160 128 = true := by decide +kernel
private theorem c1532288 : checkChunk 1532288 128 = true := by decide +kernel
private theorem c1532416 : checkChunk 1532416 128 = true := by decide +kernel
private theorem c1532544 : checkChunk 1532544 128 = true := by decide +kernel
private theorem c1532672 : checkChunk 1532672 128 = true := by decide +kernel
private theorem c1532800 : checkChunk 1532800 128 = true := by decide +kernel
private theorem c1532928 : checkChunk 1532928 128 = true := by decide +kernel
private theorem c1533056 : checkChunk 1533056 128 = true := by decide +kernel
private theorem c1533184 : checkChunk 1533184 128 = true := by decide +kernel
private theorem c1533312 : checkChunk 1533312 128 = true := by decide +kernel
private theorem c1533440 : checkChunk 1533440 128 = true := by decide +kernel
private theorem c1533568 : checkChunk 1533568 128 = true := by decide +kernel
private theorem c1533696 : checkChunk 1533696 128 = true := by decide +kernel
private theorem c1533824 : checkChunk 1533824 128 = true := by decide +kernel
private theorem c1533952 : checkChunk 1533952 128 = true := by decide +kernel
private theorem c1534080 : checkChunk 1534080 128 = true := by decide +kernel
private theorem c1534208 : checkChunk 1534208 128 = true := by decide +kernel
private theorem c1534336 : checkChunk 1534336 128 = true := by decide +kernel
private theorem c1534464 : checkChunk 1534464 128 = true := by decide +kernel
private theorem c1534592 : checkChunk 1534592 128 = true := by decide +kernel
private theorem c1534720 : checkChunk 1534720 128 = true := by decide +kernel
private theorem c1534848 : checkChunk 1534848 128 = true := by decide +kernel
private theorem c1534976 : checkChunk 1534976 128 = true := by decide +kernel
private theorem c1535104 : checkChunk 1535104 128 = true := by decide +kernel
private theorem c1535232 : checkChunk 1535232 128 = true := by decide +kernel
private theorem c1535360 : checkChunk 1535360 128 = true := by decide +kernel
private theorem c1535488 : checkChunk 1535488 128 = true := by decide +kernel
private theorem c1535616 : checkChunk 1535616 128 = true := by decide +kernel
private theorem c1535744 : checkChunk 1535744 128 = true := by decide +kernel
private theorem c1535872 : checkChunk 1535872 128 = true := by decide +kernel
private theorem c1536000 : checkChunk 1536000 128 = true := by decide +kernel
private theorem c1536128 : checkChunk 1536128 128 = true := by decide +kernel
private theorem c1536256 : checkChunk 1536256 128 = true := by decide +kernel
private theorem c1536384 : checkChunk 1536384 128 = true := by decide +kernel
private theorem c1536512 : checkChunk 1536512 128 = true := by decide +kernel
private theorem c1536640 : checkChunk 1536640 128 = true := by decide +kernel
private theorem c1536768 : checkChunk 1536768 128 = true := by decide +kernel
private theorem c1536896 : checkChunk 1536896 128 = true := by decide +kernel
private theorem c1537024 : checkChunk 1537024 128 = true := by decide +kernel
private theorem c1537152 : checkChunk 1537152 128 = true := by decide +kernel
private theorem c1537280 : checkChunk 1537280 128 = true := by decide +kernel
private theorem c1537408 : checkChunk 1537408 128 = true := by decide +kernel
private theorem c1537536 : checkChunk 1537536 128 = true := by decide +kernel
private theorem c1537664 : checkChunk 1537664 128 = true := by decide +kernel
private theorem c1537792 : checkChunk 1537792 128 = true := by decide +kernel
private theorem c1537920 : checkChunk 1537920 128 = true := by decide +kernel
private theorem c1538048 : checkChunk 1538048 128 = true := by decide +kernel
private theorem c1538176 : checkChunk 1538176 128 = true := by decide +kernel
private theorem c1538304 : checkChunk 1538304 128 = true := by decide +kernel
private theorem c1538432 : checkChunk 1538432 128 = true := by decide +kernel
private theorem c1538560 : checkChunk 1538560 128 = true := by decide +kernel
private theorem c1538688 : checkChunk 1538688 128 = true := by decide +kernel
private theorem c1538816 : checkChunk 1538816 128 = true := by decide +kernel
private theorem c1538944 : checkChunk 1538944 128 = true := by decide +kernel
private theorem c1539072 : checkChunk 1539072 128 = true := by decide +kernel
private theorem c1539200 : checkChunk 1539200 128 = true := by decide +kernel
private theorem c1539328 : checkChunk 1539328 128 = true := by decide +kernel
private theorem c1539456 : checkChunk 1539456 128 = true := by decide +kernel
private theorem c1539584 : checkChunk 1539584 128 = true := by decide +kernel
private theorem c1539712 : checkChunk 1539712 128 = true := by decide +kernel
private theorem c1539840 : checkChunk 1539840 128 = true := by decide +kernel
private theorem c1539968 : checkChunk 1539968 128 = true := by decide +kernel

public theorem checked : Checked 1531904 1540096 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1531904 128 c1531904) (checkChunk_sound 1532032 128 c1532032)) (Checked.append (checkChunk_sound 1532160 128 c1532160) (checkChunk_sound 1532288 128 c1532288))) (Checked.append (Checked.append (checkChunk_sound 1532416 128 c1532416) (checkChunk_sound 1532544 128 c1532544)) (Checked.append (checkChunk_sound 1532672 128 c1532672) (checkChunk_sound 1532800 128 c1532800)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1532928 128 c1532928) (checkChunk_sound 1533056 128 c1533056)) (Checked.append (checkChunk_sound 1533184 128 c1533184) (checkChunk_sound 1533312 128 c1533312))) (Checked.append (Checked.append (checkChunk_sound 1533440 128 c1533440) (checkChunk_sound 1533568 128 c1533568)) (Checked.append (checkChunk_sound 1533696 128 c1533696) (checkChunk_sound 1533824 128 c1533824))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1533952 128 c1533952) (checkChunk_sound 1534080 128 c1534080)) (Checked.append (checkChunk_sound 1534208 128 c1534208) (checkChunk_sound 1534336 128 c1534336))) (Checked.append (Checked.append (checkChunk_sound 1534464 128 c1534464) (checkChunk_sound 1534592 128 c1534592)) (Checked.append (checkChunk_sound 1534720 128 c1534720) (checkChunk_sound 1534848 128 c1534848)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1534976 128 c1534976) (checkChunk_sound 1535104 128 c1535104)) (Checked.append (checkChunk_sound 1535232 128 c1535232) (checkChunk_sound 1535360 128 c1535360))) (Checked.append (Checked.append (checkChunk_sound 1535488 128 c1535488) (checkChunk_sound 1535616 128 c1535616)) (Checked.append (checkChunk_sound 1535744 128 c1535744) (checkChunk_sound 1535872 128 c1535872)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1536000 128 c1536000) (checkChunk_sound 1536128 128 c1536128)) (Checked.append (checkChunk_sound 1536256 128 c1536256) (checkChunk_sound 1536384 128 c1536384))) (Checked.append (Checked.append (checkChunk_sound 1536512 128 c1536512) (checkChunk_sound 1536640 128 c1536640)) (Checked.append (checkChunk_sound 1536768 128 c1536768) (checkChunk_sound 1536896 128 c1536896)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1537024 128 c1537024) (checkChunk_sound 1537152 128 c1537152)) (Checked.append (checkChunk_sound 1537280 128 c1537280) (checkChunk_sound 1537408 128 c1537408))) (Checked.append (Checked.append (checkChunk_sound 1537536 128 c1537536) (checkChunk_sound 1537664 128 c1537664)) (Checked.append (checkChunk_sound 1537792 128 c1537792) (checkChunk_sound 1537920 128 c1537920))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1538048 128 c1538048) (checkChunk_sound 1538176 128 c1538176)) (Checked.append (checkChunk_sound 1538304 128 c1538304) (checkChunk_sound 1538432 128 c1538432))) (Checked.append (Checked.append (checkChunk_sound 1538560 128 c1538560) (checkChunk_sound 1538688 128 c1538688)) (Checked.append (checkChunk_sound 1538816 128 c1538816) (checkChunk_sound 1538944 128 c1538944)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1539072 128 c1539072) (checkChunk_sound 1539200 128 c1539200)) (Checked.append (checkChunk_sound 1539328 128 c1539328) (checkChunk_sound 1539456 128 c1539456))) (Checked.append (Checked.append (checkChunk_sound 1539584 128 c1539584) (checkChunk_sound 1539712 128 c1539712)) (Checked.append (checkChunk_sound 1539840 128 c1539840) (checkChunk_sound 1539968 128 c1539968)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B004
