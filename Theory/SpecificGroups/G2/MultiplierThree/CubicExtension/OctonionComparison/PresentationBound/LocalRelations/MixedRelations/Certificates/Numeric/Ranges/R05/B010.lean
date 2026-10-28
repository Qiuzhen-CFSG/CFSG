module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1155072, 1163264).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B010
private theorem c1155072 : checkChunk 1155072 128 = true := by decide +kernel
private theorem c1155200 : checkChunk 1155200 128 = true := by decide +kernel
private theorem c1155328 : checkChunk 1155328 128 = true := by decide +kernel
private theorem c1155456 : checkChunk 1155456 128 = true := by decide +kernel
private theorem c1155584 : checkChunk 1155584 128 = true := by decide +kernel
private theorem c1155712 : checkChunk 1155712 128 = true := by decide +kernel
private theorem c1155840 : checkChunk 1155840 128 = true := by decide +kernel
private theorem c1155968 : checkChunk 1155968 128 = true := by decide +kernel
private theorem c1156096 : checkChunk 1156096 128 = true := by decide +kernel
private theorem c1156224 : checkChunk 1156224 128 = true := by decide +kernel
private theorem c1156352 : checkChunk 1156352 128 = true := by decide +kernel
private theorem c1156480 : checkChunk 1156480 128 = true := by decide +kernel
private theorem c1156608 : checkChunk 1156608 128 = true := by decide +kernel
private theorem c1156736 : checkChunk 1156736 128 = true := by decide +kernel
private theorem c1156864 : checkChunk 1156864 128 = true := by decide +kernel
private theorem c1156992 : checkChunk 1156992 128 = true := by decide +kernel
private theorem c1157120 : checkChunk 1157120 128 = true := by decide +kernel
private theorem c1157248 : checkChunk 1157248 128 = true := by decide +kernel
private theorem c1157376 : checkChunk 1157376 128 = true := by decide +kernel
private theorem c1157504 : checkChunk 1157504 128 = true := by decide +kernel
private theorem c1157632 : checkChunk 1157632 128 = true := by decide +kernel
private theorem c1157760 : checkChunk 1157760 128 = true := by decide +kernel
private theorem c1157888 : checkChunk 1157888 128 = true := by decide +kernel
private theorem c1158016 : checkChunk 1158016 128 = true := by decide +kernel
private theorem c1158144 : checkChunk 1158144 128 = true := by decide +kernel
private theorem c1158272 : checkChunk 1158272 128 = true := by decide +kernel
private theorem c1158400 : checkChunk 1158400 128 = true := by decide +kernel
private theorem c1158528 : checkChunk 1158528 128 = true := by decide +kernel
private theorem c1158656 : checkChunk 1158656 128 = true := by decide +kernel
private theorem c1158784 : checkChunk 1158784 128 = true := by decide +kernel
private theorem c1158912 : checkChunk 1158912 128 = true := by decide +kernel
private theorem c1159040 : checkChunk 1159040 128 = true := by decide +kernel
private theorem c1159168 : checkChunk 1159168 128 = true := by decide +kernel
private theorem c1159296 : checkChunk 1159296 128 = true := by decide +kernel
private theorem c1159424 : checkChunk 1159424 128 = true := by decide +kernel
private theorem c1159552 : checkChunk 1159552 128 = true := by decide +kernel
private theorem c1159680 : checkChunk 1159680 128 = true := by decide +kernel
private theorem c1159808 : checkChunk 1159808 128 = true := by decide +kernel
private theorem c1159936 : checkChunk 1159936 128 = true := by decide +kernel
private theorem c1160064 : checkChunk 1160064 128 = true := by decide +kernel
private theorem c1160192 : checkChunk 1160192 128 = true := by decide +kernel
private theorem c1160320 : checkChunk 1160320 128 = true := by decide +kernel
private theorem c1160448 : checkChunk 1160448 128 = true := by decide +kernel
private theorem c1160576 : checkChunk 1160576 128 = true := by decide +kernel
private theorem c1160704 : checkChunk 1160704 128 = true := by decide +kernel
private theorem c1160832 : checkChunk 1160832 128 = true := by decide +kernel
private theorem c1160960 : checkChunk 1160960 128 = true := by decide +kernel
private theorem c1161088 : checkChunk 1161088 128 = true := by decide +kernel
private theorem c1161216 : checkChunk 1161216 128 = true := by decide +kernel
private theorem c1161344 : checkChunk 1161344 128 = true := by decide +kernel
private theorem c1161472 : checkChunk 1161472 128 = true := by decide +kernel
private theorem c1161600 : checkChunk 1161600 128 = true := by decide +kernel
private theorem c1161728 : checkChunk 1161728 128 = true := by decide +kernel
private theorem c1161856 : checkChunk 1161856 128 = true := by decide +kernel
private theorem c1161984 : checkChunk 1161984 128 = true := by decide +kernel
private theorem c1162112 : checkChunk 1162112 128 = true := by decide +kernel
private theorem c1162240 : checkChunk 1162240 128 = true := by decide +kernel
private theorem c1162368 : checkChunk 1162368 128 = true := by decide +kernel
private theorem c1162496 : checkChunk 1162496 128 = true := by decide +kernel
private theorem c1162624 : checkChunk 1162624 128 = true := by decide +kernel
private theorem c1162752 : checkChunk 1162752 128 = true := by decide +kernel
private theorem c1162880 : checkChunk 1162880 128 = true := by decide +kernel
private theorem c1163008 : checkChunk 1163008 128 = true := by decide +kernel
private theorem c1163136 : checkChunk 1163136 128 = true := by decide +kernel

public theorem checked : Checked 1155072 1163264 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1155072 128 c1155072) (checkChunk_sound 1155200 128 c1155200)) (Checked.append (checkChunk_sound 1155328 128 c1155328) (checkChunk_sound 1155456 128 c1155456))) (Checked.append (Checked.append (checkChunk_sound 1155584 128 c1155584) (checkChunk_sound 1155712 128 c1155712)) (Checked.append (checkChunk_sound 1155840 128 c1155840) (checkChunk_sound 1155968 128 c1155968)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1156096 128 c1156096) (checkChunk_sound 1156224 128 c1156224)) (Checked.append (checkChunk_sound 1156352 128 c1156352) (checkChunk_sound 1156480 128 c1156480))) (Checked.append (Checked.append (checkChunk_sound 1156608 128 c1156608) (checkChunk_sound 1156736 128 c1156736)) (Checked.append (checkChunk_sound 1156864 128 c1156864) (checkChunk_sound 1156992 128 c1156992))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1157120 128 c1157120) (checkChunk_sound 1157248 128 c1157248)) (Checked.append (checkChunk_sound 1157376 128 c1157376) (checkChunk_sound 1157504 128 c1157504))) (Checked.append (Checked.append (checkChunk_sound 1157632 128 c1157632) (checkChunk_sound 1157760 128 c1157760)) (Checked.append (checkChunk_sound 1157888 128 c1157888) (checkChunk_sound 1158016 128 c1158016)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1158144 128 c1158144) (checkChunk_sound 1158272 128 c1158272)) (Checked.append (checkChunk_sound 1158400 128 c1158400) (checkChunk_sound 1158528 128 c1158528))) (Checked.append (Checked.append (checkChunk_sound 1158656 128 c1158656) (checkChunk_sound 1158784 128 c1158784)) (Checked.append (checkChunk_sound 1158912 128 c1158912) (checkChunk_sound 1159040 128 c1159040)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1159168 128 c1159168) (checkChunk_sound 1159296 128 c1159296)) (Checked.append (checkChunk_sound 1159424 128 c1159424) (checkChunk_sound 1159552 128 c1159552))) (Checked.append (Checked.append (checkChunk_sound 1159680 128 c1159680) (checkChunk_sound 1159808 128 c1159808)) (Checked.append (checkChunk_sound 1159936 128 c1159936) (checkChunk_sound 1160064 128 c1160064)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1160192 128 c1160192) (checkChunk_sound 1160320 128 c1160320)) (Checked.append (checkChunk_sound 1160448 128 c1160448) (checkChunk_sound 1160576 128 c1160576))) (Checked.append (Checked.append (checkChunk_sound 1160704 128 c1160704) (checkChunk_sound 1160832 128 c1160832)) (Checked.append (checkChunk_sound 1160960 128 c1160960) (checkChunk_sound 1161088 128 c1161088))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1161216 128 c1161216) (checkChunk_sound 1161344 128 c1161344)) (Checked.append (checkChunk_sound 1161472 128 c1161472) (checkChunk_sound 1161600 128 c1161600))) (Checked.append (Checked.append (checkChunk_sound 1161728 128 c1161728) (checkChunk_sound 1161856 128 c1161856)) (Checked.append (checkChunk_sound 1161984 128 c1161984) (checkChunk_sound 1162112 128 c1162112)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1162240 128 c1162240) (checkChunk_sound 1162368 128 c1162368)) (Checked.append (checkChunk_sound 1162496 128 c1162496) (checkChunk_sound 1162624 128 c1162624))) (Checked.append (Checked.append (checkChunk_sound 1162752 128 c1162752) (checkChunk_sound 1162880 128 c1162880)) (Checked.append (checkChunk_sound 1163008 128 c1163008) (checkChunk_sound 1163136 128 c1163136)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B010
