module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1245184, 1253376).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B021
private theorem c1245184 : checkChunk 1245184 128 = true := by decide +kernel
private theorem c1245312 : checkChunk 1245312 128 = true := by decide +kernel
private theorem c1245440 : checkChunk 1245440 128 = true := by decide +kernel
private theorem c1245568 : checkChunk 1245568 128 = true := by decide +kernel
private theorem c1245696 : checkChunk 1245696 128 = true := by decide +kernel
private theorem c1245824 : checkChunk 1245824 128 = true := by decide +kernel
private theorem c1245952 : checkChunk 1245952 128 = true := by decide +kernel
private theorem c1246080 : checkChunk 1246080 128 = true := by decide +kernel
private theorem c1246208 : checkChunk 1246208 128 = true := by decide +kernel
private theorem c1246336 : checkChunk 1246336 128 = true := by decide +kernel
private theorem c1246464 : checkChunk 1246464 128 = true := by decide +kernel
private theorem c1246592 : checkChunk 1246592 128 = true := by decide +kernel
private theorem c1246720 : checkChunk 1246720 128 = true := by decide +kernel
private theorem c1246848 : checkChunk 1246848 128 = true := by decide +kernel
private theorem c1246976 : checkChunk 1246976 128 = true := by decide +kernel
private theorem c1247104 : checkChunk 1247104 128 = true := by decide +kernel
private theorem c1247232 : checkChunk 1247232 128 = true := by decide +kernel
private theorem c1247360 : checkChunk 1247360 128 = true := by decide +kernel
private theorem c1247488 : checkChunk 1247488 128 = true := by decide +kernel
private theorem c1247616 : checkChunk 1247616 128 = true := by decide +kernel
private theorem c1247744 : checkChunk 1247744 128 = true := by decide +kernel
private theorem c1247872 : checkChunk 1247872 128 = true := by decide +kernel
private theorem c1248000 : checkChunk 1248000 128 = true := by decide +kernel
private theorem c1248128 : checkChunk 1248128 128 = true := by decide +kernel
private theorem c1248256 : checkChunk 1248256 128 = true := by decide +kernel
private theorem c1248384 : checkChunk 1248384 128 = true := by decide +kernel
private theorem c1248512 : checkChunk 1248512 128 = true := by decide +kernel
private theorem c1248640 : checkChunk 1248640 128 = true := by decide +kernel
private theorem c1248768 : checkChunk 1248768 128 = true := by decide +kernel
private theorem c1248896 : checkChunk 1248896 128 = true := by decide +kernel
private theorem c1249024 : checkChunk 1249024 128 = true := by decide +kernel
private theorem c1249152 : checkChunk 1249152 128 = true := by decide +kernel
private theorem c1249280 : checkChunk 1249280 128 = true := by decide +kernel
private theorem c1249408 : checkChunk 1249408 128 = true := by decide +kernel
private theorem c1249536 : checkChunk 1249536 128 = true := by decide +kernel
private theorem c1249664 : checkChunk 1249664 128 = true := by decide +kernel
private theorem c1249792 : checkChunk 1249792 128 = true := by decide +kernel
private theorem c1249920 : checkChunk 1249920 128 = true := by decide +kernel
private theorem c1250048 : checkChunk 1250048 128 = true := by decide +kernel
private theorem c1250176 : checkChunk 1250176 128 = true := by decide +kernel
private theorem c1250304 : checkChunk 1250304 128 = true := by decide +kernel
private theorem c1250432 : checkChunk 1250432 128 = true := by decide +kernel
private theorem c1250560 : checkChunk 1250560 128 = true := by decide +kernel
private theorem c1250688 : checkChunk 1250688 128 = true := by decide +kernel
private theorem c1250816 : checkChunk 1250816 128 = true := by decide +kernel
private theorem c1250944 : checkChunk 1250944 128 = true := by decide +kernel
private theorem c1251072 : checkChunk 1251072 128 = true := by decide +kernel
private theorem c1251200 : checkChunk 1251200 128 = true := by decide +kernel
private theorem c1251328 : checkChunk 1251328 128 = true := by decide +kernel
private theorem c1251456 : checkChunk 1251456 128 = true := by decide +kernel
private theorem c1251584 : checkChunk 1251584 128 = true := by decide +kernel
private theorem c1251712 : checkChunk 1251712 128 = true := by decide +kernel
private theorem c1251840 : checkChunk 1251840 128 = true := by decide +kernel
private theorem c1251968 : checkChunk 1251968 128 = true := by decide +kernel
private theorem c1252096 : checkChunk 1252096 128 = true := by decide +kernel
private theorem c1252224 : checkChunk 1252224 128 = true := by decide +kernel
private theorem c1252352 : checkChunk 1252352 128 = true := by decide +kernel
private theorem c1252480 : checkChunk 1252480 128 = true := by decide +kernel
private theorem c1252608 : checkChunk 1252608 128 = true := by decide +kernel
private theorem c1252736 : checkChunk 1252736 128 = true := by decide +kernel
private theorem c1252864 : checkChunk 1252864 128 = true := by decide +kernel
private theorem c1252992 : checkChunk 1252992 128 = true := by decide +kernel
private theorem c1253120 : checkChunk 1253120 128 = true := by decide +kernel
private theorem c1253248 : checkChunk 1253248 128 = true := by decide +kernel

public theorem checked : Checked 1245184 1253376 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1245184 128 c1245184) (checkChunk_sound 1245312 128 c1245312)) (Checked.append (checkChunk_sound 1245440 128 c1245440) (checkChunk_sound 1245568 128 c1245568))) (Checked.append (Checked.append (checkChunk_sound 1245696 128 c1245696) (checkChunk_sound 1245824 128 c1245824)) (Checked.append (checkChunk_sound 1245952 128 c1245952) (checkChunk_sound 1246080 128 c1246080)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1246208 128 c1246208) (checkChunk_sound 1246336 128 c1246336)) (Checked.append (checkChunk_sound 1246464 128 c1246464) (checkChunk_sound 1246592 128 c1246592))) (Checked.append (Checked.append (checkChunk_sound 1246720 128 c1246720) (checkChunk_sound 1246848 128 c1246848)) (Checked.append (checkChunk_sound 1246976 128 c1246976) (checkChunk_sound 1247104 128 c1247104))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1247232 128 c1247232) (checkChunk_sound 1247360 128 c1247360)) (Checked.append (checkChunk_sound 1247488 128 c1247488) (checkChunk_sound 1247616 128 c1247616))) (Checked.append (Checked.append (checkChunk_sound 1247744 128 c1247744) (checkChunk_sound 1247872 128 c1247872)) (Checked.append (checkChunk_sound 1248000 128 c1248000) (checkChunk_sound 1248128 128 c1248128)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1248256 128 c1248256) (checkChunk_sound 1248384 128 c1248384)) (Checked.append (checkChunk_sound 1248512 128 c1248512) (checkChunk_sound 1248640 128 c1248640))) (Checked.append (Checked.append (checkChunk_sound 1248768 128 c1248768) (checkChunk_sound 1248896 128 c1248896)) (Checked.append (checkChunk_sound 1249024 128 c1249024) (checkChunk_sound 1249152 128 c1249152)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1249280 128 c1249280) (checkChunk_sound 1249408 128 c1249408)) (Checked.append (checkChunk_sound 1249536 128 c1249536) (checkChunk_sound 1249664 128 c1249664))) (Checked.append (Checked.append (checkChunk_sound 1249792 128 c1249792) (checkChunk_sound 1249920 128 c1249920)) (Checked.append (checkChunk_sound 1250048 128 c1250048) (checkChunk_sound 1250176 128 c1250176)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1250304 128 c1250304) (checkChunk_sound 1250432 128 c1250432)) (Checked.append (checkChunk_sound 1250560 128 c1250560) (checkChunk_sound 1250688 128 c1250688))) (Checked.append (Checked.append (checkChunk_sound 1250816 128 c1250816) (checkChunk_sound 1250944 128 c1250944)) (Checked.append (checkChunk_sound 1251072 128 c1251072) (checkChunk_sound 1251200 128 c1251200))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1251328 128 c1251328) (checkChunk_sound 1251456 128 c1251456)) (Checked.append (checkChunk_sound 1251584 128 c1251584) (checkChunk_sound 1251712 128 c1251712))) (Checked.append (Checked.append (checkChunk_sound 1251840 128 c1251840) (checkChunk_sound 1251968 128 c1251968)) (Checked.append (checkChunk_sound 1252096 128 c1252096) (checkChunk_sound 1252224 128 c1252224)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1252352 128 c1252352) (checkChunk_sound 1252480 128 c1252480)) (Checked.append (checkChunk_sound 1252608 128 c1252608) (checkChunk_sound 1252736 128 c1252736))) (Checked.append (Checked.append (checkChunk_sound 1252864 128 c1252864) (checkChunk_sound 1252992 128 c1252992)) (Checked.append (checkChunk_sound 1253120 128 c1253120) (checkChunk_sound 1253248 128 c1253248)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B021
