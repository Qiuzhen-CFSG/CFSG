module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1187840, 1196032).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B014
private theorem c1187840 : checkChunk 1187840 128 = true := by decide +kernel
private theorem c1187968 : checkChunk 1187968 128 = true := by decide +kernel
private theorem c1188096 : checkChunk 1188096 128 = true := by decide +kernel
private theorem c1188224 : checkChunk 1188224 128 = true := by decide +kernel
private theorem c1188352 : checkChunk 1188352 128 = true := by decide +kernel
private theorem c1188480 : checkChunk 1188480 128 = true := by decide +kernel
private theorem c1188608 : checkChunk 1188608 128 = true := by decide +kernel
private theorem c1188736 : checkChunk 1188736 128 = true := by decide +kernel
private theorem c1188864 : checkChunk 1188864 128 = true := by decide +kernel
private theorem c1188992 : checkChunk 1188992 128 = true := by decide +kernel
private theorem c1189120 : checkChunk 1189120 128 = true := by decide +kernel
private theorem c1189248 : checkChunk 1189248 128 = true := by decide +kernel
private theorem c1189376 : checkChunk 1189376 128 = true := by decide +kernel
private theorem c1189504 : checkChunk 1189504 128 = true := by decide +kernel
private theorem c1189632 : checkChunk 1189632 128 = true := by decide +kernel
private theorem c1189760 : checkChunk 1189760 128 = true := by decide +kernel
private theorem c1189888 : checkChunk 1189888 128 = true := by decide +kernel
private theorem c1190016 : checkChunk 1190016 128 = true := by decide +kernel
private theorem c1190144 : checkChunk 1190144 128 = true := by decide +kernel
private theorem c1190272 : checkChunk 1190272 128 = true := by decide +kernel
private theorem c1190400 : checkChunk 1190400 128 = true := by decide +kernel
private theorem c1190528 : checkChunk 1190528 128 = true := by decide +kernel
private theorem c1190656 : checkChunk 1190656 128 = true := by decide +kernel
private theorem c1190784 : checkChunk 1190784 128 = true := by decide +kernel
private theorem c1190912 : checkChunk 1190912 128 = true := by decide +kernel
private theorem c1191040 : checkChunk 1191040 128 = true := by decide +kernel
private theorem c1191168 : checkChunk 1191168 128 = true := by decide +kernel
private theorem c1191296 : checkChunk 1191296 128 = true := by decide +kernel
private theorem c1191424 : checkChunk 1191424 128 = true := by decide +kernel
private theorem c1191552 : checkChunk 1191552 128 = true := by decide +kernel
private theorem c1191680 : checkChunk 1191680 128 = true := by decide +kernel
private theorem c1191808 : checkChunk 1191808 128 = true := by decide +kernel
private theorem c1191936 : checkChunk 1191936 128 = true := by decide +kernel
private theorem c1192064 : checkChunk 1192064 128 = true := by decide +kernel
private theorem c1192192 : checkChunk 1192192 128 = true := by decide +kernel
private theorem c1192320 : checkChunk 1192320 128 = true := by decide +kernel
private theorem c1192448 : checkChunk 1192448 128 = true := by decide +kernel
private theorem c1192576 : checkChunk 1192576 128 = true := by decide +kernel
private theorem c1192704 : checkChunk 1192704 128 = true := by decide +kernel
private theorem c1192832 : checkChunk 1192832 128 = true := by decide +kernel
private theorem c1192960 : checkChunk 1192960 128 = true := by decide +kernel
private theorem c1193088 : checkChunk 1193088 128 = true := by decide +kernel
private theorem c1193216 : checkChunk 1193216 128 = true := by decide +kernel
private theorem c1193344 : checkChunk 1193344 128 = true := by decide +kernel
private theorem c1193472 : checkChunk 1193472 128 = true := by decide +kernel
private theorem c1193600 : checkChunk 1193600 128 = true := by decide +kernel
private theorem c1193728 : checkChunk 1193728 128 = true := by decide +kernel
private theorem c1193856 : checkChunk 1193856 128 = true := by decide +kernel
private theorem c1193984 : checkChunk 1193984 128 = true := by decide +kernel
private theorem c1194112 : checkChunk 1194112 128 = true := by decide +kernel
private theorem c1194240 : checkChunk 1194240 128 = true := by decide +kernel
private theorem c1194368 : checkChunk 1194368 128 = true := by decide +kernel
private theorem c1194496 : checkChunk 1194496 128 = true := by decide +kernel
private theorem c1194624 : checkChunk 1194624 128 = true := by decide +kernel
private theorem c1194752 : checkChunk 1194752 128 = true := by decide +kernel
private theorem c1194880 : checkChunk 1194880 128 = true := by decide +kernel
private theorem c1195008 : checkChunk 1195008 128 = true := by decide +kernel
private theorem c1195136 : checkChunk 1195136 128 = true := by decide +kernel
private theorem c1195264 : checkChunk 1195264 128 = true := by decide +kernel
private theorem c1195392 : checkChunk 1195392 128 = true := by decide +kernel
private theorem c1195520 : checkChunk 1195520 128 = true := by decide +kernel
private theorem c1195648 : checkChunk 1195648 128 = true := by decide +kernel
private theorem c1195776 : checkChunk 1195776 128 = true := by decide +kernel
private theorem c1195904 : checkChunk 1195904 128 = true := by decide +kernel

public theorem checked : Checked 1187840 1196032 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1187840 128 c1187840) (checkChunk_sound 1187968 128 c1187968)) (Checked.append (checkChunk_sound 1188096 128 c1188096) (checkChunk_sound 1188224 128 c1188224))) (Checked.append (Checked.append (checkChunk_sound 1188352 128 c1188352) (checkChunk_sound 1188480 128 c1188480)) (Checked.append (checkChunk_sound 1188608 128 c1188608) (checkChunk_sound 1188736 128 c1188736)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1188864 128 c1188864) (checkChunk_sound 1188992 128 c1188992)) (Checked.append (checkChunk_sound 1189120 128 c1189120) (checkChunk_sound 1189248 128 c1189248))) (Checked.append (Checked.append (checkChunk_sound 1189376 128 c1189376) (checkChunk_sound 1189504 128 c1189504)) (Checked.append (checkChunk_sound 1189632 128 c1189632) (checkChunk_sound 1189760 128 c1189760))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1189888 128 c1189888) (checkChunk_sound 1190016 128 c1190016)) (Checked.append (checkChunk_sound 1190144 128 c1190144) (checkChunk_sound 1190272 128 c1190272))) (Checked.append (Checked.append (checkChunk_sound 1190400 128 c1190400) (checkChunk_sound 1190528 128 c1190528)) (Checked.append (checkChunk_sound 1190656 128 c1190656) (checkChunk_sound 1190784 128 c1190784)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1190912 128 c1190912) (checkChunk_sound 1191040 128 c1191040)) (Checked.append (checkChunk_sound 1191168 128 c1191168) (checkChunk_sound 1191296 128 c1191296))) (Checked.append (Checked.append (checkChunk_sound 1191424 128 c1191424) (checkChunk_sound 1191552 128 c1191552)) (Checked.append (checkChunk_sound 1191680 128 c1191680) (checkChunk_sound 1191808 128 c1191808)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1191936 128 c1191936) (checkChunk_sound 1192064 128 c1192064)) (Checked.append (checkChunk_sound 1192192 128 c1192192) (checkChunk_sound 1192320 128 c1192320))) (Checked.append (Checked.append (checkChunk_sound 1192448 128 c1192448) (checkChunk_sound 1192576 128 c1192576)) (Checked.append (checkChunk_sound 1192704 128 c1192704) (checkChunk_sound 1192832 128 c1192832)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1192960 128 c1192960) (checkChunk_sound 1193088 128 c1193088)) (Checked.append (checkChunk_sound 1193216 128 c1193216) (checkChunk_sound 1193344 128 c1193344))) (Checked.append (Checked.append (checkChunk_sound 1193472 128 c1193472) (checkChunk_sound 1193600 128 c1193600)) (Checked.append (checkChunk_sound 1193728 128 c1193728) (checkChunk_sound 1193856 128 c1193856))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1193984 128 c1193984) (checkChunk_sound 1194112 128 c1194112)) (Checked.append (checkChunk_sound 1194240 128 c1194240) (checkChunk_sound 1194368 128 c1194368))) (Checked.append (Checked.append (checkChunk_sound 1194496 128 c1194496) (checkChunk_sound 1194624 128 c1194624)) (Checked.append (checkChunk_sound 1194752 128 c1194752) (checkChunk_sound 1194880 128 c1194880)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1195008 128 c1195008) (checkChunk_sound 1195136 128 c1195136)) (Checked.append (checkChunk_sound 1195264 128 c1195264) (checkChunk_sound 1195392 128 c1195392))) (Checked.append (Checked.append (checkChunk_sound 1195520 128 c1195520) (checkChunk_sound 1195648 128 c1195648)) (Checked.append (checkChunk_sound 1195776 128 c1195776) (checkChunk_sound 1195904 128 c1195904)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B014
