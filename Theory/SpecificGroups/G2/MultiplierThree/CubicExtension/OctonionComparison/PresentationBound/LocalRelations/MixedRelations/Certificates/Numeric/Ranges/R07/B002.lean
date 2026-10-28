module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1515520, 1523712).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B002
private theorem c1515520 : checkChunk 1515520 128 = true := by decide +kernel
private theorem c1515648 : checkChunk 1515648 128 = true := by decide +kernel
private theorem c1515776 : checkChunk 1515776 128 = true := by decide +kernel
private theorem c1515904 : checkChunk 1515904 128 = true := by decide +kernel
private theorem c1516032 : checkChunk 1516032 128 = true := by decide +kernel
private theorem c1516160 : checkChunk 1516160 128 = true := by decide +kernel
private theorem c1516288 : checkChunk 1516288 128 = true := by decide +kernel
private theorem c1516416 : checkChunk 1516416 128 = true := by decide +kernel
private theorem c1516544 : checkChunk 1516544 128 = true := by decide +kernel
private theorem c1516672 : checkChunk 1516672 128 = true := by decide +kernel
private theorem c1516800 : checkChunk 1516800 128 = true := by decide +kernel
private theorem c1516928 : checkChunk 1516928 128 = true := by decide +kernel
private theorem c1517056 : checkChunk 1517056 128 = true := by decide +kernel
private theorem c1517184 : checkChunk 1517184 128 = true := by decide +kernel
private theorem c1517312 : checkChunk 1517312 128 = true := by decide +kernel
private theorem c1517440 : checkChunk 1517440 128 = true := by decide +kernel
private theorem c1517568 : checkChunk 1517568 128 = true := by decide +kernel
private theorem c1517696 : checkChunk 1517696 128 = true := by decide +kernel
private theorem c1517824 : checkChunk 1517824 128 = true := by decide +kernel
private theorem c1517952 : checkChunk 1517952 128 = true := by decide +kernel
private theorem c1518080 : checkChunk 1518080 128 = true := by decide +kernel
private theorem c1518208 : checkChunk 1518208 128 = true := by decide +kernel
private theorem c1518336 : checkChunk 1518336 128 = true := by decide +kernel
private theorem c1518464 : checkChunk 1518464 128 = true := by decide +kernel
private theorem c1518592 : checkChunk 1518592 128 = true := by decide +kernel
private theorem c1518720 : checkChunk 1518720 128 = true := by decide +kernel
private theorem c1518848 : checkChunk 1518848 128 = true := by decide +kernel
private theorem c1518976 : checkChunk 1518976 128 = true := by decide +kernel
private theorem c1519104 : checkChunk 1519104 128 = true := by decide +kernel
private theorem c1519232 : checkChunk 1519232 128 = true := by decide +kernel
private theorem c1519360 : checkChunk 1519360 128 = true := by decide +kernel
private theorem c1519488 : checkChunk 1519488 128 = true := by decide +kernel
private theorem c1519616 : checkChunk 1519616 128 = true := by decide +kernel
private theorem c1519744 : checkChunk 1519744 128 = true := by decide +kernel
private theorem c1519872 : checkChunk 1519872 128 = true := by decide +kernel
private theorem c1520000 : checkChunk 1520000 128 = true := by decide +kernel
private theorem c1520128 : checkChunk 1520128 128 = true := by decide +kernel
private theorem c1520256 : checkChunk 1520256 128 = true := by decide +kernel
private theorem c1520384 : checkChunk 1520384 128 = true := by decide +kernel
private theorem c1520512 : checkChunk 1520512 128 = true := by decide +kernel
private theorem c1520640 : checkChunk 1520640 128 = true := by decide +kernel
private theorem c1520768 : checkChunk 1520768 128 = true := by decide +kernel
private theorem c1520896 : checkChunk 1520896 128 = true := by decide +kernel
private theorem c1521024 : checkChunk 1521024 128 = true := by decide +kernel
private theorem c1521152 : checkChunk 1521152 128 = true := by decide +kernel
private theorem c1521280 : checkChunk 1521280 128 = true := by decide +kernel
private theorem c1521408 : checkChunk 1521408 128 = true := by decide +kernel
private theorem c1521536 : checkChunk 1521536 128 = true := by decide +kernel
private theorem c1521664 : checkChunk 1521664 128 = true := by decide +kernel
private theorem c1521792 : checkChunk 1521792 128 = true := by decide +kernel
private theorem c1521920 : checkChunk 1521920 128 = true := by decide +kernel
private theorem c1522048 : checkChunk 1522048 128 = true := by decide +kernel
private theorem c1522176 : checkChunk 1522176 128 = true := by decide +kernel
private theorem c1522304 : checkChunk 1522304 128 = true := by decide +kernel
private theorem c1522432 : checkChunk 1522432 128 = true := by decide +kernel
private theorem c1522560 : checkChunk 1522560 128 = true := by decide +kernel
private theorem c1522688 : checkChunk 1522688 128 = true := by decide +kernel
private theorem c1522816 : checkChunk 1522816 128 = true := by decide +kernel
private theorem c1522944 : checkChunk 1522944 128 = true := by decide +kernel
private theorem c1523072 : checkChunk 1523072 128 = true := by decide +kernel
private theorem c1523200 : checkChunk 1523200 128 = true := by decide +kernel
private theorem c1523328 : checkChunk 1523328 128 = true := by decide +kernel
private theorem c1523456 : checkChunk 1523456 128 = true := by decide +kernel
private theorem c1523584 : checkChunk 1523584 128 = true := by decide +kernel

public theorem checked : Checked 1515520 1523712 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1515520 128 c1515520) (checkChunk_sound 1515648 128 c1515648)) (Checked.append (checkChunk_sound 1515776 128 c1515776) (checkChunk_sound 1515904 128 c1515904))) (Checked.append (Checked.append (checkChunk_sound 1516032 128 c1516032) (checkChunk_sound 1516160 128 c1516160)) (Checked.append (checkChunk_sound 1516288 128 c1516288) (checkChunk_sound 1516416 128 c1516416)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1516544 128 c1516544) (checkChunk_sound 1516672 128 c1516672)) (Checked.append (checkChunk_sound 1516800 128 c1516800) (checkChunk_sound 1516928 128 c1516928))) (Checked.append (Checked.append (checkChunk_sound 1517056 128 c1517056) (checkChunk_sound 1517184 128 c1517184)) (Checked.append (checkChunk_sound 1517312 128 c1517312) (checkChunk_sound 1517440 128 c1517440))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1517568 128 c1517568) (checkChunk_sound 1517696 128 c1517696)) (Checked.append (checkChunk_sound 1517824 128 c1517824) (checkChunk_sound 1517952 128 c1517952))) (Checked.append (Checked.append (checkChunk_sound 1518080 128 c1518080) (checkChunk_sound 1518208 128 c1518208)) (Checked.append (checkChunk_sound 1518336 128 c1518336) (checkChunk_sound 1518464 128 c1518464)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1518592 128 c1518592) (checkChunk_sound 1518720 128 c1518720)) (Checked.append (checkChunk_sound 1518848 128 c1518848) (checkChunk_sound 1518976 128 c1518976))) (Checked.append (Checked.append (checkChunk_sound 1519104 128 c1519104) (checkChunk_sound 1519232 128 c1519232)) (Checked.append (checkChunk_sound 1519360 128 c1519360) (checkChunk_sound 1519488 128 c1519488)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1519616 128 c1519616) (checkChunk_sound 1519744 128 c1519744)) (Checked.append (checkChunk_sound 1519872 128 c1519872) (checkChunk_sound 1520000 128 c1520000))) (Checked.append (Checked.append (checkChunk_sound 1520128 128 c1520128) (checkChunk_sound 1520256 128 c1520256)) (Checked.append (checkChunk_sound 1520384 128 c1520384) (checkChunk_sound 1520512 128 c1520512)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1520640 128 c1520640) (checkChunk_sound 1520768 128 c1520768)) (Checked.append (checkChunk_sound 1520896 128 c1520896) (checkChunk_sound 1521024 128 c1521024))) (Checked.append (Checked.append (checkChunk_sound 1521152 128 c1521152) (checkChunk_sound 1521280 128 c1521280)) (Checked.append (checkChunk_sound 1521408 128 c1521408) (checkChunk_sound 1521536 128 c1521536))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1521664 128 c1521664) (checkChunk_sound 1521792 128 c1521792)) (Checked.append (checkChunk_sound 1521920 128 c1521920) (checkChunk_sound 1522048 128 c1522048))) (Checked.append (Checked.append (checkChunk_sound 1522176 128 c1522176) (checkChunk_sound 1522304 128 c1522304)) (Checked.append (checkChunk_sound 1522432 128 c1522432) (checkChunk_sound 1522560 128 c1522560)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1522688 128 c1522688) (checkChunk_sound 1522816 128 c1522816)) (Checked.append (checkChunk_sound 1522944 128 c1522944) (checkChunk_sound 1523072 128 c1523072))) (Checked.append (Checked.append (checkChunk_sound 1523200 128 c1523200) (checkChunk_sound 1523328 128 c1523328)) (Checked.append (checkChunk_sound 1523456 128 c1523456) (checkChunk_sound 1523584 128 c1523584)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B002
