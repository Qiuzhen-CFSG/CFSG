module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [622592, 630784).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B023
private theorem c622592 : checkChunk 622592 128 = true := by decide +kernel
private theorem c622720 : checkChunk 622720 128 = true := by decide +kernel
private theorem c622848 : checkChunk 622848 128 = true := by decide +kernel
private theorem c622976 : checkChunk 622976 128 = true := by decide +kernel
private theorem c623104 : checkChunk 623104 128 = true := by decide +kernel
private theorem c623232 : checkChunk 623232 128 = true := by decide +kernel
private theorem c623360 : checkChunk 623360 128 = true := by decide +kernel
private theorem c623488 : checkChunk 623488 128 = true := by decide +kernel
private theorem c623616 : checkChunk 623616 128 = true := by decide +kernel
private theorem c623744 : checkChunk 623744 128 = true := by decide +kernel
private theorem c623872 : checkChunk 623872 128 = true := by decide +kernel
private theorem c624000 : checkChunk 624000 128 = true := by decide +kernel
private theorem c624128 : checkChunk 624128 128 = true := by decide +kernel
private theorem c624256 : checkChunk 624256 128 = true := by decide +kernel
private theorem c624384 : checkChunk 624384 128 = true := by decide +kernel
private theorem c624512 : checkChunk 624512 128 = true := by decide +kernel
private theorem c624640 : checkChunk 624640 128 = true := by decide +kernel
private theorem c624768 : checkChunk 624768 128 = true := by decide +kernel
private theorem c624896 : checkChunk 624896 128 = true := by decide +kernel
private theorem c625024 : checkChunk 625024 128 = true := by decide +kernel
private theorem c625152 : checkChunk 625152 128 = true := by decide +kernel
private theorem c625280 : checkChunk 625280 128 = true := by decide +kernel
private theorem c625408 : checkChunk 625408 128 = true := by decide +kernel
private theorem c625536 : checkChunk 625536 128 = true := by decide +kernel
private theorem c625664 : checkChunk 625664 128 = true := by decide +kernel
private theorem c625792 : checkChunk 625792 128 = true := by decide +kernel
private theorem c625920 : checkChunk 625920 128 = true := by decide +kernel
private theorem c626048 : checkChunk 626048 128 = true := by decide +kernel
private theorem c626176 : checkChunk 626176 128 = true := by decide +kernel
private theorem c626304 : checkChunk 626304 128 = true := by decide +kernel
private theorem c626432 : checkChunk 626432 128 = true := by decide +kernel
private theorem c626560 : checkChunk 626560 128 = true := by decide +kernel
private theorem c626688 : checkChunk 626688 128 = true := by decide +kernel
private theorem c626816 : checkChunk 626816 128 = true := by decide +kernel
private theorem c626944 : checkChunk 626944 128 = true := by decide +kernel
private theorem c627072 : checkChunk 627072 128 = true := by decide +kernel
private theorem c627200 : checkChunk 627200 128 = true := by decide +kernel
private theorem c627328 : checkChunk 627328 128 = true := by decide +kernel
private theorem c627456 : checkChunk 627456 128 = true := by decide +kernel
private theorem c627584 : checkChunk 627584 128 = true := by decide +kernel
private theorem c627712 : checkChunk 627712 128 = true := by decide +kernel
private theorem c627840 : checkChunk 627840 128 = true := by decide +kernel
private theorem c627968 : checkChunk 627968 128 = true := by decide +kernel
private theorem c628096 : checkChunk 628096 128 = true := by decide +kernel
private theorem c628224 : checkChunk 628224 128 = true := by decide +kernel
private theorem c628352 : checkChunk 628352 128 = true := by decide +kernel
private theorem c628480 : checkChunk 628480 128 = true := by decide +kernel
private theorem c628608 : checkChunk 628608 128 = true := by decide +kernel
private theorem c628736 : checkChunk 628736 128 = true := by decide +kernel
private theorem c628864 : checkChunk 628864 128 = true := by decide +kernel
private theorem c628992 : checkChunk 628992 128 = true := by decide +kernel
private theorem c629120 : checkChunk 629120 128 = true := by decide +kernel
private theorem c629248 : checkChunk 629248 128 = true := by decide +kernel
private theorem c629376 : checkChunk 629376 128 = true := by decide +kernel
private theorem c629504 : checkChunk 629504 128 = true := by decide +kernel
private theorem c629632 : checkChunk 629632 128 = true := by decide +kernel
private theorem c629760 : checkChunk 629760 128 = true := by decide +kernel
private theorem c629888 : checkChunk 629888 128 = true := by decide +kernel
private theorem c630016 : checkChunk 630016 128 = true := by decide +kernel
private theorem c630144 : checkChunk 630144 128 = true := by decide +kernel
private theorem c630272 : checkChunk 630272 128 = true := by decide +kernel
private theorem c630400 : checkChunk 630400 128 = true := by decide +kernel
private theorem c630528 : checkChunk 630528 128 = true := by decide +kernel
private theorem c630656 : checkChunk 630656 128 = true := by decide +kernel

public theorem checked : Checked 622592 630784 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 622592 128 c622592) (checkChunk_sound 622720 128 c622720)) (Checked.append (checkChunk_sound 622848 128 c622848) (checkChunk_sound 622976 128 c622976))) (Checked.append (Checked.append (checkChunk_sound 623104 128 c623104) (checkChunk_sound 623232 128 c623232)) (Checked.append (checkChunk_sound 623360 128 c623360) (checkChunk_sound 623488 128 c623488)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 623616 128 c623616) (checkChunk_sound 623744 128 c623744)) (Checked.append (checkChunk_sound 623872 128 c623872) (checkChunk_sound 624000 128 c624000))) (Checked.append (Checked.append (checkChunk_sound 624128 128 c624128) (checkChunk_sound 624256 128 c624256)) (Checked.append (checkChunk_sound 624384 128 c624384) (checkChunk_sound 624512 128 c624512))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 624640 128 c624640) (checkChunk_sound 624768 128 c624768)) (Checked.append (checkChunk_sound 624896 128 c624896) (checkChunk_sound 625024 128 c625024))) (Checked.append (Checked.append (checkChunk_sound 625152 128 c625152) (checkChunk_sound 625280 128 c625280)) (Checked.append (checkChunk_sound 625408 128 c625408) (checkChunk_sound 625536 128 c625536)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 625664 128 c625664) (checkChunk_sound 625792 128 c625792)) (Checked.append (checkChunk_sound 625920 128 c625920) (checkChunk_sound 626048 128 c626048))) (Checked.append (Checked.append (checkChunk_sound 626176 128 c626176) (checkChunk_sound 626304 128 c626304)) (Checked.append (checkChunk_sound 626432 128 c626432) (checkChunk_sound 626560 128 c626560)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 626688 128 c626688) (checkChunk_sound 626816 128 c626816)) (Checked.append (checkChunk_sound 626944 128 c626944) (checkChunk_sound 627072 128 c627072))) (Checked.append (Checked.append (checkChunk_sound 627200 128 c627200) (checkChunk_sound 627328 128 c627328)) (Checked.append (checkChunk_sound 627456 128 c627456) (checkChunk_sound 627584 128 c627584)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 627712 128 c627712) (checkChunk_sound 627840 128 c627840)) (Checked.append (checkChunk_sound 627968 128 c627968) (checkChunk_sound 628096 128 c628096))) (Checked.append (Checked.append (checkChunk_sound 628224 128 c628224) (checkChunk_sound 628352 128 c628352)) (Checked.append (checkChunk_sound 628480 128 c628480) (checkChunk_sound 628608 128 c628608))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 628736 128 c628736) (checkChunk_sound 628864 128 c628864)) (Checked.append (checkChunk_sound 628992 128 c628992) (checkChunk_sound 629120 128 c629120))) (Checked.append (Checked.append (checkChunk_sound 629248 128 c629248) (checkChunk_sound 629376 128 c629376)) (Checked.append (checkChunk_sound 629504 128 c629504) (checkChunk_sound 629632 128 c629632)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 629760 128 c629760) (checkChunk_sound 629888 128 c629888)) (Checked.append (checkChunk_sound 630016 128 c630016) (checkChunk_sound 630144 128 c630144))) (Checked.append (Checked.append (checkChunk_sound 630272 128 c630272) (checkChunk_sound 630400 128 c630400)) (Checked.append (checkChunk_sound 630528 128 c630528) (checkChunk_sound 630656 128 c630656)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B023
