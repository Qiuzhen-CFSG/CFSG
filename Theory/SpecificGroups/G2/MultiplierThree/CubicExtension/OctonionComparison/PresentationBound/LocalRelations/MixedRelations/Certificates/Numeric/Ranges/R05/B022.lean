module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1253376, 1261568).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B022
private theorem c1253376 : checkChunk 1253376 128 = true := by decide +kernel
private theorem c1253504 : checkChunk 1253504 128 = true := by decide +kernel
private theorem c1253632 : checkChunk 1253632 128 = true := by decide +kernel
private theorem c1253760 : checkChunk 1253760 128 = true := by decide +kernel
private theorem c1253888 : checkChunk 1253888 128 = true := by decide +kernel
private theorem c1254016 : checkChunk 1254016 128 = true := by decide +kernel
private theorem c1254144 : checkChunk 1254144 128 = true := by decide +kernel
private theorem c1254272 : checkChunk 1254272 128 = true := by decide +kernel
private theorem c1254400 : checkChunk 1254400 128 = true := by decide +kernel
private theorem c1254528 : checkChunk 1254528 128 = true := by decide +kernel
private theorem c1254656 : checkChunk 1254656 128 = true := by decide +kernel
private theorem c1254784 : checkChunk 1254784 128 = true := by decide +kernel
private theorem c1254912 : checkChunk 1254912 128 = true := by decide +kernel
private theorem c1255040 : checkChunk 1255040 128 = true := by decide +kernel
private theorem c1255168 : checkChunk 1255168 128 = true := by decide +kernel
private theorem c1255296 : checkChunk 1255296 128 = true := by decide +kernel
private theorem c1255424 : checkChunk 1255424 128 = true := by decide +kernel
private theorem c1255552 : checkChunk 1255552 128 = true := by decide +kernel
private theorem c1255680 : checkChunk 1255680 128 = true := by decide +kernel
private theorem c1255808 : checkChunk 1255808 128 = true := by decide +kernel
private theorem c1255936 : checkChunk 1255936 128 = true := by decide +kernel
private theorem c1256064 : checkChunk 1256064 128 = true := by decide +kernel
private theorem c1256192 : checkChunk 1256192 128 = true := by decide +kernel
private theorem c1256320 : checkChunk 1256320 128 = true := by decide +kernel
private theorem c1256448 : checkChunk 1256448 128 = true := by decide +kernel
private theorem c1256576 : checkChunk 1256576 128 = true := by decide +kernel
private theorem c1256704 : checkChunk 1256704 128 = true := by decide +kernel
private theorem c1256832 : checkChunk 1256832 128 = true := by decide +kernel
private theorem c1256960 : checkChunk 1256960 128 = true := by decide +kernel
private theorem c1257088 : checkChunk 1257088 128 = true := by decide +kernel
private theorem c1257216 : checkChunk 1257216 128 = true := by decide +kernel
private theorem c1257344 : checkChunk 1257344 128 = true := by decide +kernel
private theorem c1257472 : checkChunk 1257472 128 = true := by decide +kernel
private theorem c1257600 : checkChunk 1257600 128 = true := by decide +kernel
private theorem c1257728 : checkChunk 1257728 128 = true := by decide +kernel
private theorem c1257856 : checkChunk 1257856 128 = true := by decide +kernel
private theorem c1257984 : checkChunk 1257984 128 = true := by decide +kernel
private theorem c1258112 : checkChunk 1258112 128 = true := by decide +kernel
private theorem c1258240 : checkChunk 1258240 128 = true := by decide +kernel
private theorem c1258368 : checkChunk 1258368 128 = true := by decide +kernel
private theorem c1258496 : checkChunk 1258496 128 = true := by decide +kernel
private theorem c1258624 : checkChunk 1258624 128 = true := by decide +kernel
private theorem c1258752 : checkChunk 1258752 128 = true := by decide +kernel
private theorem c1258880 : checkChunk 1258880 128 = true := by decide +kernel
private theorem c1259008 : checkChunk 1259008 128 = true := by decide +kernel
private theorem c1259136 : checkChunk 1259136 128 = true := by decide +kernel
private theorem c1259264 : checkChunk 1259264 128 = true := by decide +kernel
private theorem c1259392 : checkChunk 1259392 128 = true := by decide +kernel
private theorem c1259520 : checkChunk 1259520 128 = true := by decide +kernel
private theorem c1259648 : checkChunk 1259648 128 = true := by decide +kernel
private theorem c1259776 : checkChunk 1259776 128 = true := by decide +kernel
private theorem c1259904 : checkChunk 1259904 128 = true := by decide +kernel
private theorem c1260032 : checkChunk 1260032 128 = true := by decide +kernel
private theorem c1260160 : checkChunk 1260160 128 = true := by decide +kernel
private theorem c1260288 : checkChunk 1260288 128 = true := by decide +kernel
private theorem c1260416 : checkChunk 1260416 128 = true := by decide +kernel
private theorem c1260544 : checkChunk 1260544 128 = true := by decide +kernel
private theorem c1260672 : checkChunk 1260672 128 = true := by decide +kernel
private theorem c1260800 : checkChunk 1260800 128 = true := by decide +kernel
private theorem c1260928 : checkChunk 1260928 128 = true := by decide +kernel
private theorem c1261056 : checkChunk 1261056 128 = true := by decide +kernel
private theorem c1261184 : checkChunk 1261184 128 = true := by decide +kernel
private theorem c1261312 : checkChunk 1261312 128 = true := by decide +kernel
private theorem c1261440 : checkChunk 1261440 128 = true := by decide +kernel

public theorem checked : Checked 1253376 1261568 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1253376 128 c1253376) (checkChunk_sound 1253504 128 c1253504)) (Checked.append (checkChunk_sound 1253632 128 c1253632) (checkChunk_sound 1253760 128 c1253760))) (Checked.append (Checked.append (checkChunk_sound 1253888 128 c1253888) (checkChunk_sound 1254016 128 c1254016)) (Checked.append (checkChunk_sound 1254144 128 c1254144) (checkChunk_sound 1254272 128 c1254272)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1254400 128 c1254400) (checkChunk_sound 1254528 128 c1254528)) (Checked.append (checkChunk_sound 1254656 128 c1254656) (checkChunk_sound 1254784 128 c1254784))) (Checked.append (Checked.append (checkChunk_sound 1254912 128 c1254912) (checkChunk_sound 1255040 128 c1255040)) (Checked.append (checkChunk_sound 1255168 128 c1255168) (checkChunk_sound 1255296 128 c1255296))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1255424 128 c1255424) (checkChunk_sound 1255552 128 c1255552)) (Checked.append (checkChunk_sound 1255680 128 c1255680) (checkChunk_sound 1255808 128 c1255808))) (Checked.append (Checked.append (checkChunk_sound 1255936 128 c1255936) (checkChunk_sound 1256064 128 c1256064)) (Checked.append (checkChunk_sound 1256192 128 c1256192) (checkChunk_sound 1256320 128 c1256320)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1256448 128 c1256448) (checkChunk_sound 1256576 128 c1256576)) (Checked.append (checkChunk_sound 1256704 128 c1256704) (checkChunk_sound 1256832 128 c1256832))) (Checked.append (Checked.append (checkChunk_sound 1256960 128 c1256960) (checkChunk_sound 1257088 128 c1257088)) (Checked.append (checkChunk_sound 1257216 128 c1257216) (checkChunk_sound 1257344 128 c1257344)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1257472 128 c1257472) (checkChunk_sound 1257600 128 c1257600)) (Checked.append (checkChunk_sound 1257728 128 c1257728) (checkChunk_sound 1257856 128 c1257856))) (Checked.append (Checked.append (checkChunk_sound 1257984 128 c1257984) (checkChunk_sound 1258112 128 c1258112)) (Checked.append (checkChunk_sound 1258240 128 c1258240) (checkChunk_sound 1258368 128 c1258368)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1258496 128 c1258496) (checkChunk_sound 1258624 128 c1258624)) (Checked.append (checkChunk_sound 1258752 128 c1258752) (checkChunk_sound 1258880 128 c1258880))) (Checked.append (Checked.append (checkChunk_sound 1259008 128 c1259008) (checkChunk_sound 1259136 128 c1259136)) (Checked.append (checkChunk_sound 1259264 128 c1259264) (checkChunk_sound 1259392 128 c1259392))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1259520 128 c1259520) (checkChunk_sound 1259648 128 c1259648)) (Checked.append (checkChunk_sound 1259776 128 c1259776) (checkChunk_sound 1259904 128 c1259904))) (Checked.append (Checked.append (checkChunk_sound 1260032 128 c1260032) (checkChunk_sound 1260160 128 c1260160)) (Checked.append (checkChunk_sound 1260288 128 c1260288) (checkChunk_sound 1260416 128 c1260416)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1260544 128 c1260544) (checkChunk_sound 1260672 128 c1260672)) (Checked.append (checkChunk_sound 1260800 128 c1260800) (checkChunk_sound 1260928 128 c1260928))) (Checked.append (Checked.append (checkChunk_sound 1261056 128 c1261056) (checkChunk_sound 1261184 128 c1261184)) (Checked.append (checkChunk_sound 1261312 128 c1261312) (checkChunk_sound 1261440 128 c1261440)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B022
