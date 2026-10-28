module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1228800, 1236992).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B019
private theorem c1228800 : checkChunk 1228800 128 = true := by decide +kernel
private theorem c1228928 : checkChunk 1228928 128 = true := by decide +kernel
private theorem c1229056 : checkChunk 1229056 128 = true := by decide +kernel
private theorem c1229184 : checkChunk 1229184 128 = true := by decide +kernel
private theorem c1229312 : checkChunk 1229312 128 = true := by decide +kernel
private theorem c1229440 : checkChunk 1229440 128 = true := by decide +kernel
private theorem c1229568 : checkChunk 1229568 128 = true := by decide +kernel
private theorem c1229696 : checkChunk 1229696 128 = true := by decide +kernel
private theorem c1229824 : checkChunk 1229824 128 = true := by decide +kernel
private theorem c1229952 : checkChunk 1229952 128 = true := by decide +kernel
private theorem c1230080 : checkChunk 1230080 128 = true := by decide +kernel
private theorem c1230208 : checkChunk 1230208 128 = true := by decide +kernel
private theorem c1230336 : checkChunk 1230336 128 = true := by decide +kernel
private theorem c1230464 : checkChunk 1230464 128 = true := by decide +kernel
private theorem c1230592 : checkChunk 1230592 128 = true := by decide +kernel
private theorem c1230720 : checkChunk 1230720 128 = true := by decide +kernel
private theorem c1230848 : checkChunk 1230848 128 = true := by decide +kernel
private theorem c1230976 : checkChunk 1230976 128 = true := by decide +kernel
private theorem c1231104 : checkChunk 1231104 128 = true := by decide +kernel
private theorem c1231232 : checkChunk 1231232 128 = true := by decide +kernel
private theorem c1231360 : checkChunk 1231360 128 = true := by decide +kernel
private theorem c1231488 : checkChunk 1231488 128 = true := by decide +kernel
private theorem c1231616 : checkChunk 1231616 128 = true := by decide +kernel
private theorem c1231744 : checkChunk 1231744 128 = true := by decide +kernel
private theorem c1231872 : checkChunk 1231872 128 = true := by decide +kernel
private theorem c1232000 : checkChunk 1232000 128 = true := by decide +kernel
private theorem c1232128 : checkChunk 1232128 128 = true := by decide +kernel
private theorem c1232256 : checkChunk 1232256 128 = true := by decide +kernel
private theorem c1232384 : checkChunk 1232384 128 = true := by decide +kernel
private theorem c1232512 : checkChunk 1232512 128 = true := by decide +kernel
private theorem c1232640 : checkChunk 1232640 128 = true := by decide +kernel
private theorem c1232768 : checkChunk 1232768 128 = true := by decide +kernel
private theorem c1232896 : checkChunk 1232896 128 = true := by decide +kernel
private theorem c1233024 : checkChunk 1233024 128 = true := by decide +kernel
private theorem c1233152 : checkChunk 1233152 128 = true := by decide +kernel
private theorem c1233280 : checkChunk 1233280 128 = true := by decide +kernel
private theorem c1233408 : checkChunk 1233408 128 = true := by decide +kernel
private theorem c1233536 : checkChunk 1233536 128 = true := by decide +kernel
private theorem c1233664 : checkChunk 1233664 128 = true := by decide +kernel
private theorem c1233792 : checkChunk 1233792 128 = true := by decide +kernel
private theorem c1233920 : checkChunk 1233920 128 = true := by decide +kernel
private theorem c1234048 : checkChunk 1234048 128 = true := by decide +kernel
private theorem c1234176 : checkChunk 1234176 128 = true := by decide +kernel
private theorem c1234304 : checkChunk 1234304 128 = true := by decide +kernel
private theorem c1234432 : checkChunk 1234432 128 = true := by decide +kernel
private theorem c1234560 : checkChunk 1234560 128 = true := by decide +kernel
private theorem c1234688 : checkChunk 1234688 128 = true := by decide +kernel
private theorem c1234816 : checkChunk 1234816 128 = true := by decide +kernel
private theorem c1234944 : checkChunk 1234944 128 = true := by decide +kernel
private theorem c1235072 : checkChunk 1235072 128 = true := by decide +kernel
private theorem c1235200 : checkChunk 1235200 128 = true := by decide +kernel
private theorem c1235328 : checkChunk 1235328 128 = true := by decide +kernel
private theorem c1235456 : checkChunk 1235456 128 = true := by decide +kernel
private theorem c1235584 : checkChunk 1235584 128 = true := by decide +kernel
private theorem c1235712 : checkChunk 1235712 128 = true := by decide +kernel
private theorem c1235840 : checkChunk 1235840 128 = true := by decide +kernel
private theorem c1235968 : checkChunk 1235968 128 = true := by decide +kernel
private theorem c1236096 : checkChunk 1236096 128 = true := by decide +kernel
private theorem c1236224 : checkChunk 1236224 128 = true := by decide +kernel
private theorem c1236352 : checkChunk 1236352 128 = true := by decide +kernel
private theorem c1236480 : checkChunk 1236480 128 = true := by decide +kernel
private theorem c1236608 : checkChunk 1236608 128 = true := by decide +kernel
private theorem c1236736 : checkChunk 1236736 128 = true := by decide +kernel
private theorem c1236864 : checkChunk 1236864 128 = true := by decide +kernel

public theorem checked : Checked 1228800 1236992 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1228800 128 c1228800) (checkChunk_sound 1228928 128 c1228928)) (Checked.append (checkChunk_sound 1229056 128 c1229056) (checkChunk_sound 1229184 128 c1229184))) (Checked.append (Checked.append (checkChunk_sound 1229312 128 c1229312) (checkChunk_sound 1229440 128 c1229440)) (Checked.append (checkChunk_sound 1229568 128 c1229568) (checkChunk_sound 1229696 128 c1229696)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1229824 128 c1229824) (checkChunk_sound 1229952 128 c1229952)) (Checked.append (checkChunk_sound 1230080 128 c1230080) (checkChunk_sound 1230208 128 c1230208))) (Checked.append (Checked.append (checkChunk_sound 1230336 128 c1230336) (checkChunk_sound 1230464 128 c1230464)) (Checked.append (checkChunk_sound 1230592 128 c1230592) (checkChunk_sound 1230720 128 c1230720))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1230848 128 c1230848) (checkChunk_sound 1230976 128 c1230976)) (Checked.append (checkChunk_sound 1231104 128 c1231104) (checkChunk_sound 1231232 128 c1231232))) (Checked.append (Checked.append (checkChunk_sound 1231360 128 c1231360) (checkChunk_sound 1231488 128 c1231488)) (Checked.append (checkChunk_sound 1231616 128 c1231616) (checkChunk_sound 1231744 128 c1231744)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1231872 128 c1231872) (checkChunk_sound 1232000 128 c1232000)) (Checked.append (checkChunk_sound 1232128 128 c1232128) (checkChunk_sound 1232256 128 c1232256))) (Checked.append (Checked.append (checkChunk_sound 1232384 128 c1232384) (checkChunk_sound 1232512 128 c1232512)) (Checked.append (checkChunk_sound 1232640 128 c1232640) (checkChunk_sound 1232768 128 c1232768)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1232896 128 c1232896) (checkChunk_sound 1233024 128 c1233024)) (Checked.append (checkChunk_sound 1233152 128 c1233152) (checkChunk_sound 1233280 128 c1233280))) (Checked.append (Checked.append (checkChunk_sound 1233408 128 c1233408) (checkChunk_sound 1233536 128 c1233536)) (Checked.append (checkChunk_sound 1233664 128 c1233664) (checkChunk_sound 1233792 128 c1233792)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1233920 128 c1233920) (checkChunk_sound 1234048 128 c1234048)) (Checked.append (checkChunk_sound 1234176 128 c1234176) (checkChunk_sound 1234304 128 c1234304))) (Checked.append (Checked.append (checkChunk_sound 1234432 128 c1234432) (checkChunk_sound 1234560 128 c1234560)) (Checked.append (checkChunk_sound 1234688 128 c1234688) (checkChunk_sound 1234816 128 c1234816))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1234944 128 c1234944) (checkChunk_sound 1235072 128 c1235072)) (Checked.append (checkChunk_sound 1235200 128 c1235200) (checkChunk_sound 1235328 128 c1235328))) (Checked.append (Checked.append (checkChunk_sound 1235456 128 c1235456) (checkChunk_sound 1235584 128 c1235584)) (Checked.append (checkChunk_sound 1235712 128 c1235712) (checkChunk_sound 1235840 128 c1235840)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1235968 128 c1235968) (checkChunk_sound 1236096 128 c1236096)) (Checked.append (checkChunk_sound 1236224 128 c1236224) (checkChunk_sound 1236352 128 c1236352))) (Checked.append (Checked.append (checkChunk_sound 1236480 128 c1236480) (checkChunk_sound 1236608 128 c1236608)) (Checked.append (checkChunk_sound 1236736 128 c1236736) (checkChunk_sound 1236864 128 c1236864)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B019
