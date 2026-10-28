module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1081344, 1089536).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B001
private theorem c1081344 : checkChunk 1081344 128 = true := by decide +kernel
private theorem c1081472 : checkChunk 1081472 128 = true := by decide +kernel
private theorem c1081600 : checkChunk 1081600 128 = true := by decide +kernel
private theorem c1081728 : checkChunk 1081728 128 = true := by decide +kernel
private theorem c1081856 : checkChunk 1081856 128 = true := by decide +kernel
private theorem c1081984 : checkChunk 1081984 128 = true := by decide +kernel
private theorem c1082112 : checkChunk 1082112 128 = true := by decide +kernel
private theorem c1082240 : checkChunk 1082240 128 = true := by decide +kernel
private theorem c1082368 : checkChunk 1082368 128 = true := by decide +kernel
private theorem c1082496 : checkChunk 1082496 128 = true := by decide +kernel
private theorem c1082624 : checkChunk 1082624 128 = true := by decide +kernel
private theorem c1082752 : checkChunk 1082752 128 = true := by decide +kernel
private theorem c1082880 : checkChunk 1082880 128 = true := by decide +kernel
private theorem c1083008 : checkChunk 1083008 128 = true := by decide +kernel
private theorem c1083136 : checkChunk 1083136 128 = true := by decide +kernel
private theorem c1083264 : checkChunk 1083264 128 = true := by decide +kernel
private theorem c1083392 : checkChunk 1083392 128 = true := by decide +kernel
private theorem c1083520 : checkChunk 1083520 128 = true := by decide +kernel
private theorem c1083648 : checkChunk 1083648 128 = true := by decide +kernel
private theorem c1083776 : checkChunk 1083776 128 = true := by decide +kernel
private theorem c1083904 : checkChunk 1083904 128 = true := by decide +kernel
private theorem c1084032 : checkChunk 1084032 128 = true := by decide +kernel
private theorem c1084160 : checkChunk 1084160 128 = true := by decide +kernel
private theorem c1084288 : checkChunk 1084288 128 = true := by decide +kernel
private theorem c1084416 : checkChunk 1084416 128 = true := by decide +kernel
private theorem c1084544 : checkChunk 1084544 128 = true := by decide +kernel
private theorem c1084672 : checkChunk 1084672 128 = true := by decide +kernel
private theorem c1084800 : checkChunk 1084800 128 = true := by decide +kernel
private theorem c1084928 : checkChunk 1084928 128 = true := by decide +kernel
private theorem c1085056 : checkChunk 1085056 128 = true := by decide +kernel
private theorem c1085184 : checkChunk 1085184 128 = true := by decide +kernel
private theorem c1085312 : checkChunk 1085312 128 = true := by decide +kernel
private theorem c1085440 : checkChunk 1085440 128 = true := by decide +kernel
private theorem c1085568 : checkChunk 1085568 128 = true := by decide +kernel
private theorem c1085696 : checkChunk 1085696 128 = true := by decide +kernel
private theorem c1085824 : checkChunk 1085824 128 = true := by decide +kernel
private theorem c1085952 : checkChunk 1085952 128 = true := by decide +kernel
private theorem c1086080 : checkChunk 1086080 128 = true := by decide +kernel
private theorem c1086208 : checkChunk 1086208 128 = true := by decide +kernel
private theorem c1086336 : checkChunk 1086336 128 = true := by decide +kernel
private theorem c1086464 : checkChunk 1086464 128 = true := by decide +kernel
private theorem c1086592 : checkChunk 1086592 128 = true := by decide +kernel
private theorem c1086720 : checkChunk 1086720 128 = true := by decide +kernel
private theorem c1086848 : checkChunk 1086848 128 = true := by decide +kernel
private theorem c1086976 : checkChunk 1086976 128 = true := by decide +kernel
private theorem c1087104 : checkChunk 1087104 128 = true := by decide +kernel
private theorem c1087232 : checkChunk 1087232 128 = true := by decide +kernel
private theorem c1087360 : checkChunk 1087360 128 = true := by decide +kernel
private theorem c1087488 : checkChunk 1087488 128 = true := by decide +kernel
private theorem c1087616 : checkChunk 1087616 128 = true := by decide +kernel
private theorem c1087744 : checkChunk 1087744 128 = true := by decide +kernel
private theorem c1087872 : checkChunk 1087872 128 = true := by decide +kernel
private theorem c1088000 : checkChunk 1088000 128 = true := by decide +kernel
private theorem c1088128 : checkChunk 1088128 128 = true := by decide +kernel
private theorem c1088256 : checkChunk 1088256 128 = true := by decide +kernel
private theorem c1088384 : checkChunk 1088384 128 = true := by decide +kernel
private theorem c1088512 : checkChunk 1088512 128 = true := by decide +kernel
private theorem c1088640 : checkChunk 1088640 128 = true := by decide +kernel
private theorem c1088768 : checkChunk 1088768 128 = true := by decide +kernel
private theorem c1088896 : checkChunk 1088896 128 = true := by decide +kernel
private theorem c1089024 : checkChunk 1089024 128 = true := by decide +kernel
private theorem c1089152 : checkChunk 1089152 128 = true := by decide +kernel
private theorem c1089280 : checkChunk 1089280 128 = true := by decide +kernel
private theorem c1089408 : checkChunk 1089408 128 = true := by decide +kernel

public theorem checked : Checked 1081344 1089536 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1081344 128 c1081344) (checkChunk_sound 1081472 128 c1081472)) (Checked.append (checkChunk_sound 1081600 128 c1081600) (checkChunk_sound 1081728 128 c1081728))) (Checked.append (Checked.append (checkChunk_sound 1081856 128 c1081856) (checkChunk_sound 1081984 128 c1081984)) (Checked.append (checkChunk_sound 1082112 128 c1082112) (checkChunk_sound 1082240 128 c1082240)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1082368 128 c1082368) (checkChunk_sound 1082496 128 c1082496)) (Checked.append (checkChunk_sound 1082624 128 c1082624) (checkChunk_sound 1082752 128 c1082752))) (Checked.append (Checked.append (checkChunk_sound 1082880 128 c1082880) (checkChunk_sound 1083008 128 c1083008)) (Checked.append (checkChunk_sound 1083136 128 c1083136) (checkChunk_sound 1083264 128 c1083264))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1083392 128 c1083392) (checkChunk_sound 1083520 128 c1083520)) (Checked.append (checkChunk_sound 1083648 128 c1083648) (checkChunk_sound 1083776 128 c1083776))) (Checked.append (Checked.append (checkChunk_sound 1083904 128 c1083904) (checkChunk_sound 1084032 128 c1084032)) (Checked.append (checkChunk_sound 1084160 128 c1084160) (checkChunk_sound 1084288 128 c1084288)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1084416 128 c1084416) (checkChunk_sound 1084544 128 c1084544)) (Checked.append (checkChunk_sound 1084672 128 c1084672) (checkChunk_sound 1084800 128 c1084800))) (Checked.append (Checked.append (checkChunk_sound 1084928 128 c1084928) (checkChunk_sound 1085056 128 c1085056)) (Checked.append (checkChunk_sound 1085184 128 c1085184) (checkChunk_sound 1085312 128 c1085312)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1085440 128 c1085440) (checkChunk_sound 1085568 128 c1085568)) (Checked.append (checkChunk_sound 1085696 128 c1085696) (checkChunk_sound 1085824 128 c1085824))) (Checked.append (Checked.append (checkChunk_sound 1085952 128 c1085952) (checkChunk_sound 1086080 128 c1086080)) (Checked.append (checkChunk_sound 1086208 128 c1086208) (checkChunk_sound 1086336 128 c1086336)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1086464 128 c1086464) (checkChunk_sound 1086592 128 c1086592)) (Checked.append (checkChunk_sound 1086720 128 c1086720) (checkChunk_sound 1086848 128 c1086848))) (Checked.append (Checked.append (checkChunk_sound 1086976 128 c1086976) (checkChunk_sound 1087104 128 c1087104)) (Checked.append (checkChunk_sound 1087232 128 c1087232) (checkChunk_sound 1087360 128 c1087360))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1087488 128 c1087488) (checkChunk_sound 1087616 128 c1087616)) (Checked.append (checkChunk_sound 1087744 128 c1087744) (checkChunk_sound 1087872 128 c1087872))) (Checked.append (Checked.append (checkChunk_sound 1088000 128 c1088000) (checkChunk_sound 1088128 128 c1088128)) (Checked.append (checkChunk_sound 1088256 128 c1088256) (checkChunk_sound 1088384 128 c1088384)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1088512 128 c1088512) (checkChunk_sound 1088640 128 c1088640)) (Checked.append (checkChunk_sound 1088768 128 c1088768) (checkChunk_sound 1088896 128 c1088896))) (Checked.append (Checked.append (checkChunk_sound 1089024 128 c1089024) (checkChunk_sound 1089152 128 c1089152)) (Checked.append (checkChunk_sound 1089280 128 c1089280) (checkChunk_sound 1089408 128 c1089408)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B001
