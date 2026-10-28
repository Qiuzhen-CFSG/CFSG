module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [843776, 851968).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B024
private theorem c843776 : checkChunk 843776 128 = true := by decide +kernel
private theorem c843904 : checkChunk 843904 128 = true := by decide +kernel
private theorem c844032 : checkChunk 844032 128 = true := by decide +kernel
private theorem c844160 : checkChunk 844160 128 = true := by decide +kernel
private theorem c844288 : checkChunk 844288 128 = true := by decide +kernel
private theorem c844416 : checkChunk 844416 128 = true := by decide +kernel
private theorem c844544 : checkChunk 844544 128 = true := by decide +kernel
private theorem c844672 : checkChunk 844672 128 = true := by decide +kernel
private theorem c844800 : checkChunk 844800 128 = true := by decide +kernel
private theorem c844928 : checkChunk 844928 128 = true := by decide +kernel
private theorem c845056 : checkChunk 845056 128 = true := by decide +kernel
private theorem c845184 : checkChunk 845184 128 = true := by decide +kernel
private theorem c845312 : checkChunk 845312 128 = true := by decide +kernel
private theorem c845440 : checkChunk 845440 128 = true := by decide +kernel
private theorem c845568 : checkChunk 845568 128 = true := by decide +kernel
private theorem c845696 : checkChunk 845696 128 = true := by decide +kernel
private theorem c845824 : checkChunk 845824 128 = true := by decide +kernel
private theorem c845952 : checkChunk 845952 128 = true := by decide +kernel
private theorem c846080 : checkChunk 846080 128 = true := by decide +kernel
private theorem c846208 : checkChunk 846208 128 = true := by decide +kernel
private theorem c846336 : checkChunk 846336 128 = true := by decide +kernel
private theorem c846464 : checkChunk 846464 128 = true := by decide +kernel
private theorem c846592 : checkChunk 846592 128 = true := by decide +kernel
private theorem c846720 : checkChunk 846720 128 = true := by decide +kernel
private theorem c846848 : checkChunk 846848 128 = true := by decide +kernel
private theorem c846976 : checkChunk 846976 128 = true := by decide +kernel
private theorem c847104 : checkChunk 847104 128 = true := by decide +kernel
private theorem c847232 : checkChunk 847232 128 = true := by decide +kernel
private theorem c847360 : checkChunk 847360 128 = true := by decide +kernel
private theorem c847488 : checkChunk 847488 128 = true := by decide +kernel
private theorem c847616 : checkChunk 847616 128 = true := by decide +kernel
private theorem c847744 : checkChunk 847744 128 = true := by decide +kernel
private theorem c847872 : checkChunk 847872 128 = true := by decide +kernel
private theorem c848000 : checkChunk 848000 128 = true := by decide +kernel
private theorem c848128 : checkChunk 848128 128 = true := by decide +kernel
private theorem c848256 : checkChunk 848256 128 = true := by decide +kernel
private theorem c848384 : checkChunk 848384 128 = true := by decide +kernel
private theorem c848512 : checkChunk 848512 128 = true := by decide +kernel
private theorem c848640 : checkChunk 848640 128 = true := by decide +kernel
private theorem c848768 : checkChunk 848768 128 = true := by decide +kernel
private theorem c848896 : checkChunk 848896 128 = true := by decide +kernel
private theorem c849024 : checkChunk 849024 128 = true := by decide +kernel
private theorem c849152 : checkChunk 849152 128 = true := by decide +kernel
private theorem c849280 : checkChunk 849280 128 = true := by decide +kernel
private theorem c849408 : checkChunk 849408 128 = true := by decide +kernel
private theorem c849536 : checkChunk 849536 128 = true := by decide +kernel
private theorem c849664 : checkChunk 849664 128 = true := by decide +kernel
private theorem c849792 : checkChunk 849792 128 = true := by decide +kernel
private theorem c849920 : checkChunk 849920 128 = true := by decide +kernel
private theorem c850048 : checkChunk 850048 128 = true := by decide +kernel
private theorem c850176 : checkChunk 850176 128 = true := by decide +kernel
private theorem c850304 : checkChunk 850304 128 = true := by decide +kernel
private theorem c850432 : checkChunk 850432 128 = true := by decide +kernel
private theorem c850560 : checkChunk 850560 128 = true := by decide +kernel
private theorem c850688 : checkChunk 850688 128 = true := by decide +kernel
private theorem c850816 : checkChunk 850816 128 = true := by decide +kernel
private theorem c850944 : checkChunk 850944 128 = true := by decide +kernel
private theorem c851072 : checkChunk 851072 128 = true := by decide +kernel
private theorem c851200 : checkChunk 851200 128 = true := by decide +kernel
private theorem c851328 : checkChunk 851328 128 = true := by decide +kernel
private theorem c851456 : checkChunk 851456 128 = true := by decide +kernel
private theorem c851584 : checkChunk 851584 128 = true := by decide +kernel
private theorem c851712 : checkChunk 851712 128 = true := by decide +kernel
private theorem c851840 : checkChunk 851840 128 = true := by decide +kernel

public theorem checked : Checked 843776 851968 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 843776 128 c843776) (checkChunk_sound 843904 128 c843904)) (Checked.append (checkChunk_sound 844032 128 c844032) (checkChunk_sound 844160 128 c844160))) (Checked.append (Checked.append (checkChunk_sound 844288 128 c844288) (checkChunk_sound 844416 128 c844416)) (Checked.append (checkChunk_sound 844544 128 c844544) (checkChunk_sound 844672 128 c844672)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 844800 128 c844800) (checkChunk_sound 844928 128 c844928)) (Checked.append (checkChunk_sound 845056 128 c845056) (checkChunk_sound 845184 128 c845184))) (Checked.append (Checked.append (checkChunk_sound 845312 128 c845312) (checkChunk_sound 845440 128 c845440)) (Checked.append (checkChunk_sound 845568 128 c845568) (checkChunk_sound 845696 128 c845696))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 845824 128 c845824) (checkChunk_sound 845952 128 c845952)) (Checked.append (checkChunk_sound 846080 128 c846080) (checkChunk_sound 846208 128 c846208))) (Checked.append (Checked.append (checkChunk_sound 846336 128 c846336) (checkChunk_sound 846464 128 c846464)) (Checked.append (checkChunk_sound 846592 128 c846592) (checkChunk_sound 846720 128 c846720)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 846848 128 c846848) (checkChunk_sound 846976 128 c846976)) (Checked.append (checkChunk_sound 847104 128 c847104) (checkChunk_sound 847232 128 c847232))) (Checked.append (Checked.append (checkChunk_sound 847360 128 c847360) (checkChunk_sound 847488 128 c847488)) (Checked.append (checkChunk_sound 847616 128 c847616) (checkChunk_sound 847744 128 c847744)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 847872 128 c847872) (checkChunk_sound 848000 128 c848000)) (Checked.append (checkChunk_sound 848128 128 c848128) (checkChunk_sound 848256 128 c848256))) (Checked.append (Checked.append (checkChunk_sound 848384 128 c848384) (checkChunk_sound 848512 128 c848512)) (Checked.append (checkChunk_sound 848640 128 c848640) (checkChunk_sound 848768 128 c848768)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 848896 128 c848896) (checkChunk_sound 849024 128 c849024)) (Checked.append (checkChunk_sound 849152 128 c849152) (checkChunk_sound 849280 128 c849280))) (Checked.append (Checked.append (checkChunk_sound 849408 128 c849408) (checkChunk_sound 849536 128 c849536)) (Checked.append (checkChunk_sound 849664 128 c849664) (checkChunk_sound 849792 128 c849792))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 849920 128 c849920) (checkChunk_sound 850048 128 c850048)) (Checked.append (checkChunk_sound 850176 128 c850176) (checkChunk_sound 850304 128 c850304))) (Checked.append (Checked.append (checkChunk_sound 850432 128 c850432) (checkChunk_sound 850560 128 c850560)) (Checked.append (checkChunk_sound 850688 128 c850688) (checkChunk_sound 850816 128 c850816)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 850944 128 c850944) (checkChunk_sound 851072 128 c851072)) (Checked.append (checkChunk_sound 851200 128 c851200) (checkChunk_sound 851328 128 c851328))) (Checked.append (Checked.append (checkChunk_sound 851456 128 c851456) (checkChunk_sound 851584 128 c851584)) (Checked.append (checkChunk_sound 851712 128 c851712) (checkChunk_sound 851840 128 c851840)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B024
