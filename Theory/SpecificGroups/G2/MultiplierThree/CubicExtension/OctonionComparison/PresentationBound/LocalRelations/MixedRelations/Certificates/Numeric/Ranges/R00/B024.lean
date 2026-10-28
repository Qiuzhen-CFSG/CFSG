module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [204800, 212992).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B024
private theorem c204800 : checkChunk 204800 128 = true := by decide +kernel
private theorem c204928 : checkChunk 204928 128 = true := by decide +kernel
private theorem c205056 : checkChunk 205056 128 = true := by decide +kernel
private theorem c205184 : checkChunk 205184 128 = true := by decide +kernel
private theorem c205312 : checkChunk 205312 128 = true := by decide +kernel
private theorem c205440 : checkChunk 205440 128 = true := by decide +kernel
private theorem c205568 : checkChunk 205568 128 = true := by decide +kernel
private theorem c205696 : checkChunk 205696 128 = true := by decide +kernel
private theorem c205824 : checkChunk 205824 128 = true := by decide +kernel
private theorem c205952 : checkChunk 205952 128 = true := by decide +kernel
private theorem c206080 : checkChunk 206080 128 = true := by decide +kernel
private theorem c206208 : checkChunk 206208 128 = true := by decide +kernel
private theorem c206336 : checkChunk 206336 128 = true := by decide +kernel
private theorem c206464 : checkChunk 206464 128 = true := by decide +kernel
private theorem c206592 : checkChunk 206592 128 = true := by decide +kernel
private theorem c206720 : checkChunk 206720 128 = true := by decide +kernel
private theorem c206848 : checkChunk 206848 128 = true := by decide +kernel
private theorem c206976 : checkChunk 206976 128 = true := by decide +kernel
private theorem c207104 : checkChunk 207104 128 = true := by decide +kernel
private theorem c207232 : checkChunk 207232 128 = true := by decide +kernel
private theorem c207360 : checkChunk 207360 128 = true := by decide +kernel
private theorem c207488 : checkChunk 207488 128 = true := by decide +kernel
private theorem c207616 : checkChunk 207616 128 = true := by decide +kernel
private theorem c207744 : checkChunk 207744 128 = true := by decide +kernel
private theorem c207872 : checkChunk 207872 128 = true := by decide +kernel
private theorem c208000 : checkChunk 208000 128 = true := by decide +kernel
private theorem c208128 : checkChunk 208128 128 = true := by decide +kernel
private theorem c208256 : checkChunk 208256 128 = true := by decide +kernel
private theorem c208384 : checkChunk 208384 128 = true := by decide +kernel
private theorem c208512 : checkChunk 208512 128 = true := by decide +kernel
private theorem c208640 : checkChunk 208640 128 = true := by decide +kernel
private theorem c208768 : checkChunk 208768 128 = true := by decide +kernel
private theorem c208896 : checkChunk 208896 128 = true := by decide +kernel
private theorem c209024 : checkChunk 209024 128 = true := by decide +kernel
private theorem c209152 : checkChunk 209152 128 = true := by decide +kernel
private theorem c209280 : checkChunk 209280 128 = true := by decide +kernel
private theorem c209408 : checkChunk 209408 128 = true := by decide +kernel
private theorem c209536 : checkChunk 209536 128 = true := by decide +kernel
private theorem c209664 : checkChunk 209664 128 = true := by decide +kernel
private theorem c209792 : checkChunk 209792 128 = true := by decide +kernel
private theorem c209920 : checkChunk 209920 128 = true := by decide +kernel
private theorem c210048 : checkChunk 210048 128 = true := by decide +kernel
private theorem c210176 : checkChunk 210176 128 = true := by decide +kernel
private theorem c210304 : checkChunk 210304 128 = true := by decide +kernel
private theorem c210432 : checkChunk 210432 128 = true := by decide +kernel
private theorem c210560 : checkChunk 210560 128 = true := by decide +kernel
private theorem c210688 : checkChunk 210688 128 = true := by decide +kernel
private theorem c210816 : checkChunk 210816 128 = true := by decide +kernel
private theorem c210944 : checkChunk 210944 128 = true := by decide +kernel
private theorem c211072 : checkChunk 211072 128 = true := by decide +kernel
private theorem c211200 : checkChunk 211200 128 = true := by decide +kernel
private theorem c211328 : checkChunk 211328 128 = true := by decide +kernel
private theorem c211456 : checkChunk 211456 128 = true := by decide +kernel
private theorem c211584 : checkChunk 211584 128 = true := by decide +kernel
private theorem c211712 : checkChunk 211712 128 = true := by decide +kernel
private theorem c211840 : checkChunk 211840 128 = true := by decide +kernel
private theorem c211968 : checkChunk 211968 128 = true := by decide +kernel
private theorem c212096 : checkChunk 212096 128 = true := by decide +kernel
private theorem c212224 : checkChunk 212224 128 = true := by decide +kernel
private theorem c212352 : checkChunk 212352 128 = true := by decide +kernel
private theorem c212480 : checkChunk 212480 128 = true := by decide +kernel
private theorem c212608 : checkChunk 212608 128 = true := by decide +kernel
private theorem c212736 : checkChunk 212736 128 = true := by decide +kernel
private theorem c212864 : checkChunk 212864 128 = true := by decide +kernel

public theorem checked : Checked 204800 212992 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 204800 128 c204800) (checkChunk_sound 204928 128 c204928)) (Checked.append (checkChunk_sound 205056 128 c205056) (checkChunk_sound 205184 128 c205184))) (Checked.append (Checked.append (checkChunk_sound 205312 128 c205312) (checkChunk_sound 205440 128 c205440)) (Checked.append (checkChunk_sound 205568 128 c205568) (checkChunk_sound 205696 128 c205696)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 205824 128 c205824) (checkChunk_sound 205952 128 c205952)) (Checked.append (checkChunk_sound 206080 128 c206080) (checkChunk_sound 206208 128 c206208))) (Checked.append (Checked.append (checkChunk_sound 206336 128 c206336) (checkChunk_sound 206464 128 c206464)) (Checked.append (checkChunk_sound 206592 128 c206592) (checkChunk_sound 206720 128 c206720))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 206848 128 c206848) (checkChunk_sound 206976 128 c206976)) (Checked.append (checkChunk_sound 207104 128 c207104) (checkChunk_sound 207232 128 c207232))) (Checked.append (Checked.append (checkChunk_sound 207360 128 c207360) (checkChunk_sound 207488 128 c207488)) (Checked.append (checkChunk_sound 207616 128 c207616) (checkChunk_sound 207744 128 c207744)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 207872 128 c207872) (checkChunk_sound 208000 128 c208000)) (Checked.append (checkChunk_sound 208128 128 c208128) (checkChunk_sound 208256 128 c208256))) (Checked.append (Checked.append (checkChunk_sound 208384 128 c208384) (checkChunk_sound 208512 128 c208512)) (Checked.append (checkChunk_sound 208640 128 c208640) (checkChunk_sound 208768 128 c208768)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 208896 128 c208896) (checkChunk_sound 209024 128 c209024)) (Checked.append (checkChunk_sound 209152 128 c209152) (checkChunk_sound 209280 128 c209280))) (Checked.append (Checked.append (checkChunk_sound 209408 128 c209408) (checkChunk_sound 209536 128 c209536)) (Checked.append (checkChunk_sound 209664 128 c209664) (checkChunk_sound 209792 128 c209792)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 209920 128 c209920) (checkChunk_sound 210048 128 c210048)) (Checked.append (checkChunk_sound 210176 128 c210176) (checkChunk_sound 210304 128 c210304))) (Checked.append (Checked.append (checkChunk_sound 210432 128 c210432) (checkChunk_sound 210560 128 c210560)) (Checked.append (checkChunk_sound 210688 128 c210688) (checkChunk_sound 210816 128 c210816))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 210944 128 c210944) (checkChunk_sound 211072 128 c211072)) (Checked.append (checkChunk_sound 211200 128 c211200) (checkChunk_sound 211328 128 c211328))) (Checked.append (Checked.append (checkChunk_sound 211456 128 c211456) (checkChunk_sound 211584 128 c211584)) (Checked.append (checkChunk_sound 211712 128 c211712) (checkChunk_sound 211840 128 c211840)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 211968 128 c211968) (checkChunk_sound 212096 128 c212096)) (Checked.append (checkChunk_sound 212224 128 c212224) (checkChunk_sound 212352 128 c212352))) (Checked.append (Checked.append (checkChunk_sound 212480 128 c212480) (checkChunk_sound 212608 128 c212608)) (Checked.append (checkChunk_sound 212736 128 c212736) (checkChunk_sound 212864 128 c212864)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B024
