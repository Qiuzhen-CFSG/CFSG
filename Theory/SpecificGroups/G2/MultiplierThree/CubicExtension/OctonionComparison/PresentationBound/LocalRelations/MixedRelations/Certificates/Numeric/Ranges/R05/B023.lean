module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1261568, 1269760).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B023
private theorem c1261568 : checkChunk 1261568 128 = true := by decide +kernel
private theorem c1261696 : checkChunk 1261696 128 = true := by decide +kernel
private theorem c1261824 : checkChunk 1261824 128 = true := by decide +kernel
private theorem c1261952 : checkChunk 1261952 128 = true := by decide +kernel
private theorem c1262080 : checkChunk 1262080 128 = true := by decide +kernel
private theorem c1262208 : checkChunk 1262208 128 = true := by decide +kernel
private theorem c1262336 : checkChunk 1262336 128 = true := by decide +kernel
private theorem c1262464 : checkChunk 1262464 128 = true := by decide +kernel
private theorem c1262592 : checkChunk 1262592 128 = true := by decide +kernel
private theorem c1262720 : checkChunk 1262720 128 = true := by decide +kernel
private theorem c1262848 : checkChunk 1262848 128 = true := by decide +kernel
private theorem c1262976 : checkChunk 1262976 128 = true := by decide +kernel
private theorem c1263104 : checkChunk 1263104 128 = true := by decide +kernel
private theorem c1263232 : checkChunk 1263232 128 = true := by decide +kernel
private theorem c1263360 : checkChunk 1263360 128 = true := by decide +kernel
private theorem c1263488 : checkChunk 1263488 128 = true := by decide +kernel
private theorem c1263616 : checkChunk 1263616 128 = true := by decide +kernel
private theorem c1263744 : checkChunk 1263744 128 = true := by decide +kernel
private theorem c1263872 : checkChunk 1263872 128 = true := by decide +kernel
private theorem c1264000 : checkChunk 1264000 128 = true := by decide +kernel
private theorem c1264128 : checkChunk 1264128 128 = true := by decide +kernel
private theorem c1264256 : checkChunk 1264256 128 = true := by decide +kernel
private theorem c1264384 : checkChunk 1264384 128 = true := by decide +kernel
private theorem c1264512 : checkChunk 1264512 128 = true := by decide +kernel
private theorem c1264640 : checkChunk 1264640 128 = true := by decide +kernel
private theorem c1264768 : checkChunk 1264768 128 = true := by decide +kernel
private theorem c1264896 : checkChunk 1264896 128 = true := by decide +kernel
private theorem c1265024 : checkChunk 1265024 128 = true := by decide +kernel
private theorem c1265152 : checkChunk 1265152 128 = true := by decide +kernel
private theorem c1265280 : checkChunk 1265280 128 = true := by decide +kernel
private theorem c1265408 : checkChunk 1265408 128 = true := by decide +kernel
private theorem c1265536 : checkChunk 1265536 128 = true := by decide +kernel
private theorem c1265664 : checkChunk 1265664 128 = true := by decide +kernel
private theorem c1265792 : checkChunk 1265792 128 = true := by decide +kernel
private theorem c1265920 : checkChunk 1265920 128 = true := by decide +kernel
private theorem c1266048 : checkChunk 1266048 128 = true := by decide +kernel
private theorem c1266176 : checkChunk 1266176 128 = true := by decide +kernel
private theorem c1266304 : checkChunk 1266304 128 = true := by decide +kernel
private theorem c1266432 : checkChunk 1266432 128 = true := by decide +kernel
private theorem c1266560 : checkChunk 1266560 128 = true := by decide +kernel
private theorem c1266688 : checkChunk 1266688 128 = true := by decide +kernel
private theorem c1266816 : checkChunk 1266816 128 = true := by decide +kernel
private theorem c1266944 : checkChunk 1266944 128 = true := by decide +kernel
private theorem c1267072 : checkChunk 1267072 128 = true := by decide +kernel
private theorem c1267200 : checkChunk 1267200 128 = true := by decide +kernel
private theorem c1267328 : checkChunk 1267328 128 = true := by decide +kernel
private theorem c1267456 : checkChunk 1267456 128 = true := by decide +kernel
private theorem c1267584 : checkChunk 1267584 128 = true := by decide +kernel
private theorem c1267712 : checkChunk 1267712 128 = true := by decide +kernel
private theorem c1267840 : checkChunk 1267840 128 = true := by decide +kernel
private theorem c1267968 : checkChunk 1267968 128 = true := by decide +kernel
private theorem c1268096 : checkChunk 1268096 128 = true := by decide +kernel
private theorem c1268224 : checkChunk 1268224 128 = true := by decide +kernel
private theorem c1268352 : checkChunk 1268352 128 = true := by decide +kernel
private theorem c1268480 : checkChunk 1268480 128 = true := by decide +kernel
private theorem c1268608 : checkChunk 1268608 128 = true := by decide +kernel
private theorem c1268736 : checkChunk 1268736 128 = true := by decide +kernel
private theorem c1268864 : checkChunk 1268864 128 = true := by decide +kernel
private theorem c1268992 : checkChunk 1268992 128 = true := by decide +kernel
private theorem c1269120 : checkChunk 1269120 128 = true := by decide +kernel
private theorem c1269248 : checkChunk 1269248 128 = true := by decide +kernel
private theorem c1269376 : checkChunk 1269376 128 = true := by decide +kernel
private theorem c1269504 : checkChunk 1269504 128 = true := by decide +kernel
private theorem c1269632 : checkChunk 1269632 128 = true := by decide +kernel

public theorem checked : Checked 1261568 1269760 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1261568 128 c1261568) (checkChunk_sound 1261696 128 c1261696)) (Checked.append (checkChunk_sound 1261824 128 c1261824) (checkChunk_sound 1261952 128 c1261952))) (Checked.append (Checked.append (checkChunk_sound 1262080 128 c1262080) (checkChunk_sound 1262208 128 c1262208)) (Checked.append (checkChunk_sound 1262336 128 c1262336) (checkChunk_sound 1262464 128 c1262464)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1262592 128 c1262592) (checkChunk_sound 1262720 128 c1262720)) (Checked.append (checkChunk_sound 1262848 128 c1262848) (checkChunk_sound 1262976 128 c1262976))) (Checked.append (Checked.append (checkChunk_sound 1263104 128 c1263104) (checkChunk_sound 1263232 128 c1263232)) (Checked.append (checkChunk_sound 1263360 128 c1263360) (checkChunk_sound 1263488 128 c1263488))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1263616 128 c1263616) (checkChunk_sound 1263744 128 c1263744)) (Checked.append (checkChunk_sound 1263872 128 c1263872) (checkChunk_sound 1264000 128 c1264000))) (Checked.append (Checked.append (checkChunk_sound 1264128 128 c1264128) (checkChunk_sound 1264256 128 c1264256)) (Checked.append (checkChunk_sound 1264384 128 c1264384) (checkChunk_sound 1264512 128 c1264512)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1264640 128 c1264640) (checkChunk_sound 1264768 128 c1264768)) (Checked.append (checkChunk_sound 1264896 128 c1264896) (checkChunk_sound 1265024 128 c1265024))) (Checked.append (Checked.append (checkChunk_sound 1265152 128 c1265152) (checkChunk_sound 1265280 128 c1265280)) (Checked.append (checkChunk_sound 1265408 128 c1265408) (checkChunk_sound 1265536 128 c1265536)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1265664 128 c1265664) (checkChunk_sound 1265792 128 c1265792)) (Checked.append (checkChunk_sound 1265920 128 c1265920) (checkChunk_sound 1266048 128 c1266048))) (Checked.append (Checked.append (checkChunk_sound 1266176 128 c1266176) (checkChunk_sound 1266304 128 c1266304)) (Checked.append (checkChunk_sound 1266432 128 c1266432) (checkChunk_sound 1266560 128 c1266560)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1266688 128 c1266688) (checkChunk_sound 1266816 128 c1266816)) (Checked.append (checkChunk_sound 1266944 128 c1266944) (checkChunk_sound 1267072 128 c1267072))) (Checked.append (Checked.append (checkChunk_sound 1267200 128 c1267200) (checkChunk_sound 1267328 128 c1267328)) (Checked.append (checkChunk_sound 1267456 128 c1267456) (checkChunk_sound 1267584 128 c1267584))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1267712 128 c1267712) (checkChunk_sound 1267840 128 c1267840)) (Checked.append (checkChunk_sound 1267968 128 c1267968) (checkChunk_sound 1268096 128 c1268096))) (Checked.append (Checked.append (checkChunk_sound 1268224 128 c1268224) (checkChunk_sound 1268352 128 c1268352)) (Checked.append (checkChunk_sound 1268480 128 c1268480) (checkChunk_sound 1268608 128 c1268608)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1268736 128 c1268736) (checkChunk_sound 1268864 128 c1268864)) (Checked.append (checkChunk_sound 1268992 128 c1268992) (checkChunk_sound 1269120 128 c1269120))) (Checked.append (Checked.append (checkChunk_sound 1269248 128 c1269248) (checkChunk_sound 1269376 128 c1269376)) (Checked.append (checkChunk_sound 1269504 128 c1269504) (checkChunk_sound 1269632 128 c1269632)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B023
