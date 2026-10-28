module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1122304, 1130496).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B006
private theorem c1122304 : checkChunk 1122304 128 = true := by decide +kernel
private theorem c1122432 : checkChunk 1122432 128 = true := by decide +kernel
private theorem c1122560 : checkChunk 1122560 128 = true := by decide +kernel
private theorem c1122688 : checkChunk 1122688 128 = true := by decide +kernel
private theorem c1122816 : checkChunk 1122816 128 = true := by decide +kernel
private theorem c1122944 : checkChunk 1122944 128 = true := by decide +kernel
private theorem c1123072 : checkChunk 1123072 128 = true := by decide +kernel
private theorem c1123200 : checkChunk 1123200 128 = true := by decide +kernel
private theorem c1123328 : checkChunk 1123328 128 = true := by decide +kernel
private theorem c1123456 : checkChunk 1123456 128 = true := by decide +kernel
private theorem c1123584 : checkChunk 1123584 128 = true := by decide +kernel
private theorem c1123712 : checkChunk 1123712 128 = true := by decide +kernel
private theorem c1123840 : checkChunk 1123840 128 = true := by decide +kernel
private theorem c1123968 : checkChunk 1123968 128 = true := by decide +kernel
private theorem c1124096 : checkChunk 1124096 128 = true := by decide +kernel
private theorem c1124224 : checkChunk 1124224 128 = true := by decide +kernel
private theorem c1124352 : checkChunk 1124352 128 = true := by decide +kernel
private theorem c1124480 : checkChunk 1124480 128 = true := by decide +kernel
private theorem c1124608 : checkChunk 1124608 128 = true := by decide +kernel
private theorem c1124736 : checkChunk 1124736 128 = true := by decide +kernel
private theorem c1124864 : checkChunk 1124864 128 = true := by decide +kernel
private theorem c1124992 : checkChunk 1124992 128 = true := by decide +kernel
private theorem c1125120 : checkChunk 1125120 128 = true := by decide +kernel
private theorem c1125248 : checkChunk 1125248 128 = true := by decide +kernel
private theorem c1125376 : checkChunk 1125376 128 = true := by decide +kernel
private theorem c1125504 : checkChunk 1125504 128 = true := by decide +kernel
private theorem c1125632 : checkChunk 1125632 128 = true := by decide +kernel
private theorem c1125760 : checkChunk 1125760 128 = true := by decide +kernel
private theorem c1125888 : checkChunk 1125888 128 = true := by decide +kernel
private theorem c1126016 : checkChunk 1126016 128 = true := by decide +kernel
private theorem c1126144 : checkChunk 1126144 128 = true := by decide +kernel
private theorem c1126272 : checkChunk 1126272 128 = true := by decide +kernel
private theorem c1126400 : checkChunk 1126400 128 = true := by decide +kernel
private theorem c1126528 : checkChunk 1126528 128 = true := by decide +kernel
private theorem c1126656 : checkChunk 1126656 128 = true := by decide +kernel
private theorem c1126784 : checkChunk 1126784 128 = true := by decide +kernel
private theorem c1126912 : checkChunk 1126912 128 = true := by decide +kernel
private theorem c1127040 : checkChunk 1127040 128 = true := by decide +kernel
private theorem c1127168 : checkChunk 1127168 128 = true := by decide +kernel
private theorem c1127296 : checkChunk 1127296 128 = true := by decide +kernel
private theorem c1127424 : checkChunk 1127424 128 = true := by decide +kernel
private theorem c1127552 : checkChunk 1127552 128 = true := by decide +kernel
private theorem c1127680 : checkChunk 1127680 128 = true := by decide +kernel
private theorem c1127808 : checkChunk 1127808 128 = true := by decide +kernel
private theorem c1127936 : checkChunk 1127936 128 = true := by decide +kernel
private theorem c1128064 : checkChunk 1128064 128 = true := by decide +kernel
private theorem c1128192 : checkChunk 1128192 128 = true := by decide +kernel
private theorem c1128320 : checkChunk 1128320 128 = true := by decide +kernel
private theorem c1128448 : checkChunk 1128448 128 = true := by decide +kernel
private theorem c1128576 : checkChunk 1128576 128 = true := by decide +kernel
private theorem c1128704 : checkChunk 1128704 128 = true := by decide +kernel
private theorem c1128832 : checkChunk 1128832 128 = true := by decide +kernel
private theorem c1128960 : checkChunk 1128960 128 = true := by decide +kernel
private theorem c1129088 : checkChunk 1129088 128 = true := by decide +kernel
private theorem c1129216 : checkChunk 1129216 128 = true := by decide +kernel
private theorem c1129344 : checkChunk 1129344 128 = true := by decide +kernel
private theorem c1129472 : checkChunk 1129472 128 = true := by decide +kernel
private theorem c1129600 : checkChunk 1129600 128 = true := by decide +kernel
private theorem c1129728 : checkChunk 1129728 128 = true := by decide +kernel
private theorem c1129856 : checkChunk 1129856 128 = true := by decide +kernel
private theorem c1129984 : checkChunk 1129984 128 = true := by decide +kernel
private theorem c1130112 : checkChunk 1130112 128 = true := by decide +kernel
private theorem c1130240 : checkChunk 1130240 128 = true := by decide +kernel
private theorem c1130368 : checkChunk 1130368 128 = true := by decide +kernel

public theorem checked : Checked 1122304 1130496 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1122304 128 c1122304) (checkChunk_sound 1122432 128 c1122432)) (Checked.append (checkChunk_sound 1122560 128 c1122560) (checkChunk_sound 1122688 128 c1122688))) (Checked.append (Checked.append (checkChunk_sound 1122816 128 c1122816) (checkChunk_sound 1122944 128 c1122944)) (Checked.append (checkChunk_sound 1123072 128 c1123072) (checkChunk_sound 1123200 128 c1123200)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1123328 128 c1123328) (checkChunk_sound 1123456 128 c1123456)) (Checked.append (checkChunk_sound 1123584 128 c1123584) (checkChunk_sound 1123712 128 c1123712))) (Checked.append (Checked.append (checkChunk_sound 1123840 128 c1123840) (checkChunk_sound 1123968 128 c1123968)) (Checked.append (checkChunk_sound 1124096 128 c1124096) (checkChunk_sound 1124224 128 c1124224))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1124352 128 c1124352) (checkChunk_sound 1124480 128 c1124480)) (Checked.append (checkChunk_sound 1124608 128 c1124608) (checkChunk_sound 1124736 128 c1124736))) (Checked.append (Checked.append (checkChunk_sound 1124864 128 c1124864) (checkChunk_sound 1124992 128 c1124992)) (Checked.append (checkChunk_sound 1125120 128 c1125120) (checkChunk_sound 1125248 128 c1125248)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1125376 128 c1125376) (checkChunk_sound 1125504 128 c1125504)) (Checked.append (checkChunk_sound 1125632 128 c1125632) (checkChunk_sound 1125760 128 c1125760))) (Checked.append (Checked.append (checkChunk_sound 1125888 128 c1125888) (checkChunk_sound 1126016 128 c1126016)) (Checked.append (checkChunk_sound 1126144 128 c1126144) (checkChunk_sound 1126272 128 c1126272)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1126400 128 c1126400) (checkChunk_sound 1126528 128 c1126528)) (Checked.append (checkChunk_sound 1126656 128 c1126656) (checkChunk_sound 1126784 128 c1126784))) (Checked.append (Checked.append (checkChunk_sound 1126912 128 c1126912) (checkChunk_sound 1127040 128 c1127040)) (Checked.append (checkChunk_sound 1127168 128 c1127168) (checkChunk_sound 1127296 128 c1127296)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1127424 128 c1127424) (checkChunk_sound 1127552 128 c1127552)) (Checked.append (checkChunk_sound 1127680 128 c1127680) (checkChunk_sound 1127808 128 c1127808))) (Checked.append (Checked.append (checkChunk_sound 1127936 128 c1127936) (checkChunk_sound 1128064 128 c1128064)) (Checked.append (checkChunk_sound 1128192 128 c1128192) (checkChunk_sound 1128320 128 c1128320))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1128448 128 c1128448) (checkChunk_sound 1128576 128 c1128576)) (Checked.append (checkChunk_sound 1128704 128 c1128704) (checkChunk_sound 1128832 128 c1128832))) (Checked.append (Checked.append (checkChunk_sound 1128960 128 c1128960) (checkChunk_sound 1129088 128 c1129088)) (Checked.append (checkChunk_sound 1129216 128 c1129216) (checkChunk_sound 1129344 128 c1129344)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1129472 128 c1129472) (checkChunk_sound 1129600 128 c1129600)) (Checked.append (checkChunk_sound 1129728 128 c1129728) (checkChunk_sound 1129856 128 c1129856))) (Checked.append (Checked.append (checkChunk_sound 1129984 128 c1129984) (checkChunk_sound 1130112 128 c1130112)) (Checked.append (checkChunk_sound 1130240 128 c1130240) (checkChunk_sound 1130368 128 c1130368)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B006
