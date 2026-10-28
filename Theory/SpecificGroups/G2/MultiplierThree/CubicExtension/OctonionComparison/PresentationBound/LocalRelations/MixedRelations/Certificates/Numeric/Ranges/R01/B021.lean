module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [393216, 401408).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B021
private theorem c393216 : checkChunk 393216 128 = true := by decide +kernel
private theorem c393344 : checkChunk 393344 128 = true := by decide +kernel
private theorem c393472 : checkChunk 393472 128 = true := by decide +kernel
private theorem c393600 : checkChunk 393600 128 = true := by decide +kernel
private theorem c393728 : checkChunk 393728 128 = true := by decide +kernel
private theorem c393856 : checkChunk 393856 128 = true := by decide +kernel
private theorem c393984 : checkChunk 393984 128 = true := by decide +kernel
private theorem c394112 : checkChunk 394112 128 = true := by decide +kernel
private theorem c394240 : checkChunk 394240 128 = true := by decide +kernel
private theorem c394368 : checkChunk 394368 128 = true := by decide +kernel
private theorem c394496 : checkChunk 394496 128 = true := by decide +kernel
private theorem c394624 : checkChunk 394624 128 = true := by decide +kernel
private theorem c394752 : checkChunk 394752 128 = true := by decide +kernel
private theorem c394880 : checkChunk 394880 128 = true := by decide +kernel
private theorem c395008 : checkChunk 395008 128 = true := by decide +kernel
private theorem c395136 : checkChunk 395136 128 = true := by decide +kernel
private theorem c395264 : checkChunk 395264 128 = true := by decide +kernel
private theorem c395392 : checkChunk 395392 128 = true := by decide +kernel
private theorem c395520 : checkChunk 395520 128 = true := by decide +kernel
private theorem c395648 : checkChunk 395648 128 = true := by decide +kernel
private theorem c395776 : checkChunk 395776 128 = true := by decide +kernel
private theorem c395904 : checkChunk 395904 128 = true := by decide +kernel
private theorem c396032 : checkChunk 396032 128 = true := by decide +kernel
private theorem c396160 : checkChunk 396160 128 = true := by decide +kernel
private theorem c396288 : checkChunk 396288 128 = true := by decide +kernel
private theorem c396416 : checkChunk 396416 128 = true := by decide +kernel
private theorem c396544 : checkChunk 396544 128 = true := by decide +kernel
private theorem c396672 : checkChunk 396672 128 = true := by decide +kernel
private theorem c396800 : checkChunk 396800 128 = true := by decide +kernel
private theorem c396928 : checkChunk 396928 128 = true := by decide +kernel
private theorem c397056 : checkChunk 397056 128 = true := by decide +kernel
private theorem c397184 : checkChunk 397184 128 = true := by decide +kernel
private theorem c397312 : checkChunk 397312 128 = true := by decide +kernel
private theorem c397440 : checkChunk 397440 128 = true := by decide +kernel
private theorem c397568 : checkChunk 397568 128 = true := by decide +kernel
private theorem c397696 : checkChunk 397696 128 = true := by decide +kernel
private theorem c397824 : checkChunk 397824 128 = true := by decide +kernel
private theorem c397952 : checkChunk 397952 128 = true := by decide +kernel
private theorem c398080 : checkChunk 398080 128 = true := by decide +kernel
private theorem c398208 : checkChunk 398208 128 = true := by decide +kernel
private theorem c398336 : checkChunk 398336 128 = true := by decide +kernel
private theorem c398464 : checkChunk 398464 128 = true := by decide +kernel
private theorem c398592 : checkChunk 398592 128 = true := by decide +kernel
private theorem c398720 : checkChunk 398720 128 = true := by decide +kernel
private theorem c398848 : checkChunk 398848 128 = true := by decide +kernel
private theorem c398976 : checkChunk 398976 128 = true := by decide +kernel
private theorem c399104 : checkChunk 399104 128 = true := by decide +kernel
private theorem c399232 : checkChunk 399232 128 = true := by decide +kernel
private theorem c399360 : checkChunk 399360 128 = true := by decide +kernel
private theorem c399488 : checkChunk 399488 128 = true := by decide +kernel
private theorem c399616 : checkChunk 399616 128 = true := by decide +kernel
private theorem c399744 : checkChunk 399744 128 = true := by decide +kernel
private theorem c399872 : checkChunk 399872 128 = true := by decide +kernel
private theorem c400000 : checkChunk 400000 128 = true := by decide +kernel
private theorem c400128 : checkChunk 400128 128 = true := by decide +kernel
private theorem c400256 : checkChunk 400256 128 = true := by decide +kernel
private theorem c400384 : checkChunk 400384 128 = true := by decide +kernel
private theorem c400512 : checkChunk 400512 128 = true := by decide +kernel
private theorem c400640 : checkChunk 400640 128 = true := by decide +kernel
private theorem c400768 : checkChunk 400768 128 = true := by decide +kernel
private theorem c400896 : checkChunk 400896 128 = true := by decide +kernel
private theorem c401024 : checkChunk 401024 128 = true := by decide +kernel
private theorem c401152 : checkChunk 401152 128 = true := by decide +kernel
private theorem c401280 : checkChunk 401280 128 = true := by decide +kernel

public theorem checked : Checked 393216 401408 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 393216 128 c393216) (checkChunk_sound 393344 128 c393344)) (Checked.append (checkChunk_sound 393472 128 c393472) (checkChunk_sound 393600 128 c393600))) (Checked.append (Checked.append (checkChunk_sound 393728 128 c393728) (checkChunk_sound 393856 128 c393856)) (Checked.append (checkChunk_sound 393984 128 c393984) (checkChunk_sound 394112 128 c394112)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 394240 128 c394240) (checkChunk_sound 394368 128 c394368)) (Checked.append (checkChunk_sound 394496 128 c394496) (checkChunk_sound 394624 128 c394624))) (Checked.append (Checked.append (checkChunk_sound 394752 128 c394752) (checkChunk_sound 394880 128 c394880)) (Checked.append (checkChunk_sound 395008 128 c395008) (checkChunk_sound 395136 128 c395136))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 395264 128 c395264) (checkChunk_sound 395392 128 c395392)) (Checked.append (checkChunk_sound 395520 128 c395520) (checkChunk_sound 395648 128 c395648))) (Checked.append (Checked.append (checkChunk_sound 395776 128 c395776) (checkChunk_sound 395904 128 c395904)) (Checked.append (checkChunk_sound 396032 128 c396032) (checkChunk_sound 396160 128 c396160)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 396288 128 c396288) (checkChunk_sound 396416 128 c396416)) (Checked.append (checkChunk_sound 396544 128 c396544) (checkChunk_sound 396672 128 c396672))) (Checked.append (Checked.append (checkChunk_sound 396800 128 c396800) (checkChunk_sound 396928 128 c396928)) (Checked.append (checkChunk_sound 397056 128 c397056) (checkChunk_sound 397184 128 c397184)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 397312 128 c397312) (checkChunk_sound 397440 128 c397440)) (Checked.append (checkChunk_sound 397568 128 c397568) (checkChunk_sound 397696 128 c397696))) (Checked.append (Checked.append (checkChunk_sound 397824 128 c397824) (checkChunk_sound 397952 128 c397952)) (Checked.append (checkChunk_sound 398080 128 c398080) (checkChunk_sound 398208 128 c398208)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 398336 128 c398336) (checkChunk_sound 398464 128 c398464)) (Checked.append (checkChunk_sound 398592 128 c398592) (checkChunk_sound 398720 128 c398720))) (Checked.append (Checked.append (checkChunk_sound 398848 128 c398848) (checkChunk_sound 398976 128 c398976)) (Checked.append (checkChunk_sound 399104 128 c399104) (checkChunk_sound 399232 128 c399232))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 399360 128 c399360) (checkChunk_sound 399488 128 c399488)) (Checked.append (checkChunk_sound 399616 128 c399616) (checkChunk_sound 399744 128 c399744))) (Checked.append (Checked.append (checkChunk_sound 399872 128 c399872) (checkChunk_sound 400000 128 c400000)) (Checked.append (checkChunk_sound 400128 128 c400128) (checkChunk_sound 400256 128 c400256)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 400384 128 c400384) (checkChunk_sound 400512 128 c400512)) (Checked.append (checkChunk_sound 400640 128 c400640) (checkChunk_sound 400768 128 c400768))) (Checked.append (Checked.append (checkChunk_sound 400896 128 c400896) (checkChunk_sound 401024 128 c401024)) (Checked.append (checkChunk_sound 401152 128 c401152) (checkChunk_sound 401280 128 c401280)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B021
