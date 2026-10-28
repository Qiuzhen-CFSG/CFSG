module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [139264, 147456).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B016
private theorem c139264 : checkChunk 139264 128 = true := by decide +kernel
private theorem c139392 : checkChunk 139392 128 = true := by decide +kernel
private theorem c139520 : checkChunk 139520 128 = true := by decide +kernel
private theorem c139648 : checkChunk 139648 128 = true := by decide +kernel
private theorem c139776 : checkChunk 139776 128 = true := by decide +kernel
private theorem c139904 : checkChunk 139904 128 = true := by decide +kernel
private theorem c140032 : checkChunk 140032 128 = true := by decide +kernel
private theorem c140160 : checkChunk 140160 128 = true := by decide +kernel
private theorem c140288 : checkChunk 140288 128 = true := by decide +kernel
private theorem c140416 : checkChunk 140416 128 = true := by decide +kernel
private theorem c140544 : checkChunk 140544 128 = true := by decide +kernel
private theorem c140672 : checkChunk 140672 128 = true := by decide +kernel
private theorem c140800 : checkChunk 140800 128 = true := by decide +kernel
private theorem c140928 : checkChunk 140928 128 = true := by decide +kernel
private theorem c141056 : checkChunk 141056 128 = true := by decide +kernel
private theorem c141184 : checkChunk 141184 128 = true := by decide +kernel
private theorem c141312 : checkChunk 141312 128 = true := by decide +kernel
private theorem c141440 : checkChunk 141440 128 = true := by decide +kernel
private theorem c141568 : checkChunk 141568 128 = true := by decide +kernel
private theorem c141696 : checkChunk 141696 128 = true := by decide +kernel
private theorem c141824 : checkChunk 141824 128 = true := by decide +kernel
private theorem c141952 : checkChunk 141952 128 = true := by decide +kernel
private theorem c142080 : checkChunk 142080 128 = true := by decide +kernel
private theorem c142208 : checkChunk 142208 128 = true := by decide +kernel
private theorem c142336 : checkChunk 142336 128 = true := by decide +kernel
private theorem c142464 : checkChunk 142464 128 = true := by decide +kernel
private theorem c142592 : checkChunk 142592 128 = true := by decide +kernel
private theorem c142720 : checkChunk 142720 128 = true := by decide +kernel
private theorem c142848 : checkChunk 142848 128 = true := by decide +kernel
private theorem c142976 : checkChunk 142976 128 = true := by decide +kernel
private theorem c143104 : checkChunk 143104 128 = true := by decide +kernel
private theorem c143232 : checkChunk 143232 128 = true := by decide +kernel
private theorem c143360 : checkChunk 143360 128 = true := by decide +kernel
private theorem c143488 : checkChunk 143488 128 = true := by decide +kernel
private theorem c143616 : checkChunk 143616 128 = true := by decide +kernel
private theorem c143744 : checkChunk 143744 128 = true := by decide +kernel
private theorem c143872 : checkChunk 143872 128 = true := by decide +kernel
private theorem c144000 : checkChunk 144000 128 = true := by decide +kernel
private theorem c144128 : checkChunk 144128 128 = true := by decide +kernel
private theorem c144256 : checkChunk 144256 128 = true := by decide +kernel
private theorem c144384 : checkChunk 144384 128 = true := by decide +kernel
private theorem c144512 : checkChunk 144512 128 = true := by decide +kernel
private theorem c144640 : checkChunk 144640 128 = true := by decide +kernel
private theorem c144768 : checkChunk 144768 128 = true := by decide +kernel
private theorem c144896 : checkChunk 144896 128 = true := by decide +kernel
private theorem c145024 : checkChunk 145024 128 = true := by decide +kernel
private theorem c145152 : checkChunk 145152 128 = true := by decide +kernel
private theorem c145280 : checkChunk 145280 128 = true := by decide +kernel
private theorem c145408 : checkChunk 145408 128 = true := by decide +kernel
private theorem c145536 : checkChunk 145536 128 = true := by decide +kernel
private theorem c145664 : checkChunk 145664 128 = true := by decide +kernel
private theorem c145792 : checkChunk 145792 128 = true := by decide +kernel
private theorem c145920 : checkChunk 145920 128 = true := by decide +kernel
private theorem c146048 : checkChunk 146048 128 = true := by decide +kernel
private theorem c146176 : checkChunk 146176 128 = true := by decide +kernel
private theorem c146304 : checkChunk 146304 128 = true := by decide +kernel
private theorem c146432 : checkChunk 146432 128 = true := by decide +kernel
private theorem c146560 : checkChunk 146560 128 = true := by decide +kernel
private theorem c146688 : checkChunk 146688 128 = true := by decide +kernel
private theorem c146816 : checkChunk 146816 128 = true := by decide +kernel
private theorem c146944 : checkChunk 146944 128 = true := by decide +kernel
private theorem c147072 : checkChunk 147072 128 = true := by decide +kernel
private theorem c147200 : checkChunk 147200 128 = true := by decide +kernel
private theorem c147328 : checkChunk 147328 128 = true := by decide +kernel

public theorem checked : Checked 139264 147456 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 139264 128 c139264) (checkChunk_sound 139392 128 c139392)) (Checked.append (checkChunk_sound 139520 128 c139520) (checkChunk_sound 139648 128 c139648))) (Checked.append (Checked.append (checkChunk_sound 139776 128 c139776) (checkChunk_sound 139904 128 c139904)) (Checked.append (checkChunk_sound 140032 128 c140032) (checkChunk_sound 140160 128 c140160)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 140288 128 c140288) (checkChunk_sound 140416 128 c140416)) (Checked.append (checkChunk_sound 140544 128 c140544) (checkChunk_sound 140672 128 c140672))) (Checked.append (Checked.append (checkChunk_sound 140800 128 c140800) (checkChunk_sound 140928 128 c140928)) (Checked.append (checkChunk_sound 141056 128 c141056) (checkChunk_sound 141184 128 c141184))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 141312 128 c141312) (checkChunk_sound 141440 128 c141440)) (Checked.append (checkChunk_sound 141568 128 c141568) (checkChunk_sound 141696 128 c141696))) (Checked.append (Checked.append (checkChunk_sound 141824 128 c141824) (checkChunk_sound 141952 128 c141952)) (Checked.append (checkChunk_sound 142080 128 c142080) (checkChunk_sound 142208 128 c142208)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 142336 128 c142336) (checkChunk_sound 142464 128 c142464)) (Checked.append (checkChunk_sound 142592 128 c142592) (checkChunk_sound 142720 128 c142720))) (Checked.append (Checked.append (checkChunk_sound 142848 128 c142848) (checkChunk_sound 142976 128 c142976)) (Checked.append (checkChunk_sound 143104 128 c143104) (checkChunk_sound 143232 128 c143232)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 143360 128 c143360) (checkChunk_sound 143488 128 c143488)) (Checked.append (checkChunk_sound 143616 128 c143616) (checkChunk_sound 143744 128 c143744))) (Checked.append (Checked.append (checkChunk_sound 143872 128 c143872) (checkChunk_sound 144000 128 c144000)) (Checked.append (checkChunk_sound 144128 128 c144128) (checkChunk_sound 144256 128 c144256)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 144384 128 c144384) (checkChunk_sound 144512 128 c144512)) (Checked.append (checkChunk_sound 144640 128 c144640) (checkChunk_sound 144768 128 c144768))) (Checked.append (Checked.append (checkChunk_sound 144896 128 c144896) (checkChunk_sound 145024 128 c145024)) (Checked.append (checkChunk_sound 145152 128 c145152) (checkChunk_sound 145280 128 c145280))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 145408 128 c145408) (checkChunk_sound 145536 128 c145536)) (Checked.append (checkChunk_sound 145664 128 c145664) (checkChunk_sound 145792 128 c145792))) (Checked.append (Checked.append (checkChunk_sound 145920 128 c145920) (checkChunk_sound 146048 128 c146048)) (Checked.append (checkChunk_sound 146176 128 c146176) (checkChunk_sound 146304 128 c146304)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 146432 128 c146432) (checkChunk_sound 146560 128 c146560)) (Checked.append (checkChunk_sound 146688 128 c146688) (checkChunk_sound 146816 128 c146816))) (Checked.append (Checked.append (checkChunk_sound 146944 128 c146944) (checkChunk_sound 147072 128 c147072)) (Checked.append (checkChunk_sound 147200 128 c147200) (checkChunk_sound 147328 128 c147328)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B016
