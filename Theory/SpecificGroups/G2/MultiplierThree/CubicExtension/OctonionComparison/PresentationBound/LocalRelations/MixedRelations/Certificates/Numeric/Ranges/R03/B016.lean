module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [778240, 786432).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B016
private theorem c778240 : checkChunk 778240 128 = true := by decide +kernel
private theorem c778368 : checkChunk 778368 128 = true := by decide +kernel
private theorem c778496 : checkChunk 778496 128 = true := by decide +kernel
private theorem c778624 : checkChunk 778624 128 = true := by decide +kernel
private theorem c778752 : checkChunk 778752 128 = true := by decide +kernel
private theorem c778880 : checkChunk 778880 128 = true := by decide +kernel
private theorem c779008 : checkChunk 779008 128 = true := by decide +kernel
private theorem c779136 : checkChunk 779136 128 = true := by decide +kernel
private theorem c779264 : checkChunk 779264 128 = true := by decide +kernel
private theorem c779392 : checkChunk 779392 128 = true := by decide +kernel
private theorem c779520 : checkChunk 779520 128 = true := by decide +kernel
private theorem c779648 : checkChunk 779648 128 = true := by decide +kernel
private theorem c779776 : checkChunk 779776 128 = true := by decide +kernel
private theorem c779904 : checkChunk 779904 128 = true := by decide +kernel
private theorem c780032 : checkChunk 780032 128 = true := by decide +kernel
private theorem c780160 : checkChunk 780160 128 = true := by decide +kernel
private theorem c780288 : checkChunk 780288 128 = true := by decide +kernel
private theorem c780416 : checkChunk 780416 128 = true := by decide +kernel
private theorem c780544 : checkChunk 780544 128 = true := by decide +kernel
private theorem c780672 : checkChunk 780672 128 = true := by decide +kernel
private theorem c780800 : checkChunk 780800 128 = true := by decide +kernel
private theorem c780928 : checkChunk 780928 128 = true := by decide +kernel
private theorem c781056 : checkChunk 781056 128 = true := by decide +kernel
private theorem c781184 : checkChunk 781184 128 = true := by decide +kernel
private theorem c781312 : checkChunk 781312 128 = true := by decide +kernel
private theorem c781440 : checkChunk 781440 128 = true := by decide +kernel
private theorem c781568 : checkChunk 781568 128 = true := by decide +kernel
private theorem c781696 : checkChunk 781696 128 = true := by decide +kernel
private theorem c781824 : checkChunk 781824 128 = true := by decide +kernel
private theorem c781952 : checkChunk 781952 128 = true := by decide +kernel
private theorem c782080 : checkChunk 782080 128 = true := by decide +kernel
private theorem c782208 : checkChunk 782208 128 = true := by decide +kernel
private theorem c782336 : checkChunk 782336 128 = true := by decide +kernel
private theorem c782464 : checkChunk 782464 128 = true := by decide +kernel
private theorem c782592 : checkChunk 782592 128 = true := by decide +kernel
private theorem c782720 : checkChunk 782720 128 = true := by decide +kernel
private theorem c782848 : checkChunk 782848 128 = true := by decide +kernel
private theorem c782976 : checkChunk 782976 128 = true := by decide +kernel
private theorem c783104 : checkChunk 783104 128 = true := by decide +kernel
private theorem c783232 : checkChunk 783232 128 = true := by decide +kernel
private theorem c783360 : checkChunk 783360 128 = true := by decide +kernel
private theorem c783488 : checkChunk 783488 128 = true := by decide +kernel
private theorem c783616 : checkChunk 783616 128 = true := by decide +kernel
private theorem c783744 : checkChunk 783744 128 = true := by decide +kernel
private theorem c783872 : checkChunk 783872 128 = true := by decide +kernel
private theorem c784000 : checkChunk 784000 128 = true := by decide +kernel
private theorem c784128 : checkChunk 784128 128 = true := by decide +kernel
private theorem c784256 : checkChunk 784256 128 = true := by decide +kernel
private theorem c784384 : checkChunk 784384 128 = true := by decide +kernel
private theorem c784512 : checkChunk 784512 128 = true := by decide +kernel
private theorem c784640 : checkChunk 784640 128 = true := by decide +kernel
private theorem c784768 : checkChunk 784768 128 = true := by decide +kernel
private theorem c784896 : checkChunk 784896 128 = true := by decide +kernel
private theorem c785024 : checkChunk 785024 128 = true := by decide +kernel
private theorem c785152 : checkChunk 785152 128 = true := by decide +kernel
private theorem c785280 : checkChunk 785280 128 = true := by decide +kernel
private theorem c785408 : checkChunk 785408 128 = true := by decide +kernel
private theorem c785536 : checkChunk 785536 128 = true := by decide +kernel
private theorem c785664 : checkChunk 785664 128 = true := by decide +kernel
private theorem c785792 : checkChunk 785792 128 = true := by decide +kernel
private theorem c785920 : checkChunk 785920 128 = true := by decide +kernel
private theorem c786048 : checkChunk 786048 128 = true := by decide +kernel
private theorem c786176 : checkChunk 786176 128 = true := by decide +kernel
private theorem c786304 : checkChunk 786304 128 = true := by decide +kernel

public theorem checked : Checked 778240 786432 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 778240 128 c778240) (checkChunk_sound 778368 128 c778368)) (Checked.append (checkChunk_sound 778496 128 c778496) (checkChunk_sound 778624 128 c778624))) (Checked.append (Checked.append (checkChunk_sound 778752 128 c778752) (checkChunk_sound 778880 128 c778880)) (Checked.append (checkChunk_sound 779008 128 c779008) (checkChunk_sound 779136 128 c779136)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 779264 128 c779264) (checkChunk_sound 779392 128 c779392)) (Checked.append (checkChunk_sound 779520 128 c779520) (checkChunk_sound 779648 128 c779648))) (Checked.append (Checked.append (checkChunk_sound 779776 128 c779776) (checkChunk_sound 779904 128 c779904)) (Checked.append (checkChunk_sound 780032 128 c780032) (checkChunk_sound 780160 128 c780160))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 780288 128 c780288) (checkChunk_sound 780416 128 c780416)) (Checked.append (checkChunk_sound 780544 128 c780544) (checkChunk_sound 780672 128 c780672))) (Checked.append (Checked.append (checkChunk_sound 780800 128 c780800) (checkChunk_sound 780928 128 c780928)) (Checked.append (checkChunk_sound 781056 128 c781056) (checkChunk_sound 781184 128 c781184)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 781312 128 c781312) (checkChunk_sound 781440 128 c781440)) (Checked.append (checkChunk_sound 781568 128 c781568) (checkChunk_sound 781696 128 c781696))) (Checked.append (Checked.append (checkChunk_sound 781824 128 c781824) (checkChunk_sound 781952 128 c781952)) (Checked.append (checkChunk_sound 782080 128 c782080) (checkChunk_sound 782208 128 c782208)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 782336 128 c782336) (checkChunk_sound 782464 128 c782464)) (Checked.append (checkChunk_sound 782592 128 c782592) (checkChunk_sound 782720 128 c782720))) (Checked.append (Checked.append (checkChunk_sound 782848 128 c782848) (checkChunk_sound 782976 128 c782976)) (Checked.append (checkChunk_sound 783104 128 c783104) (checkChunk_sound 783232 128 c783232)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 783360 128 c783360) (checkChunk_sound 783488 128 c783488)) (Checked.append (checkChunk_sound 783616 128 c783616) (checkChunk_sound 783744 128 c783744))) (Checked.append (Checked.append (checkChunk_sound 783872 128 c783872) (checkChunk_sound 784000 128 c784000)) (Checked.append (checkChunk_sound 784128 128 c784128) (checkChunk_sound 784256 128 c784256))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 784384 128 c784384) (checkChunk_sound 784512 128 c784512)) (Checked.append (checkChunk_sound 784640 128 c784640) (checkChunk_sound 784768 128 c784768))) (Checked.append (Checked.append (checkChunk_sound 784896 128 c784896) (checkChunk_sound 785024 128 c785024)) (Checked.append (checkChunk_sound 785152 128 c785152) (checkChunk_sound 785280 128 c785280)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 785408 128 c785408) (checkChunk_sound 785536 128 c785536)) (Checked.append (checkChunk_sound 785664 128 c785664) (checkChunk_sound 785792 128 c785792))) (Checked.append (Checked.append (checkChunk_sound 785920 128 c785920) (checkChunk_sound 786048 128 c786048)) (Checked.append (checkChunk_sound 786176 128 c786176) (checkChunk_sound 786304 128 c786304)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B016
