module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1327104, 1335296).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B005
private theorem c1327104 : checkChunk 1327104 128 = true := by decide +kernel
private theorem c1327232 : checkChunk 1327232 128 = true := by decide +kernel
private theorem c1327360 : checkChunk 1327360 128 = true := by decide +kernel
private theorem c1327488 : checkChunk 1327488 128 = true := by decide +kernel
private theorem c1327616 : checkChunk 1327616 128 = true := by decide +kernel
private theorem c1327744 : checkChunk 1327744 128 = true := by decide +kernel
private theorem c1327872 : checkChunk 1327872 128 = true := by decide +kernel
private theorem c1328000 : checkChunk 1328000 128 = true := by decide +kernel
private theorem c1328128 : checkChunk 1328128 128 = true := by decide +kernel
private theorem c1328256 : checkChunk 1328256 128 = true := by decide +kernel
private theorem c1328384 : checkChunk 1328384 128 = true := by decide +kernel
private theorem c1328512 : checkChunk 1328512 128 = true := by decide +kernel
private theorem c1328640 : checkChunk 1328640 128 = true := by decide +kernel
private theorem c1328768 : checkChunk 1328768 128 = true := by decide +kernel
private theorem c1328896 : checkChunk 1328896 128 = true := by decide +kernel
private theorem c1329024 : checkChunk 1329024 128 = true := by decide +kernel
private theorem c1329152 : checkChunk 1329152 128 = true := by decide +kernel
private theorem c1329280 : checkChunk 1329280 128 = true := by decide +kernel
private theorem c1329408 : checkChunk 1329408 128 = true := by decide +kernel
private theorem c1329536 : checkChunk 1329536 128 = true := by decide +kernel
private theorem c1329664 : checkChunk 1329664 128 = true := by decide +kernel
private theorem c1329792 : checkChunk 1329792 128 = true := by decide +kernel
private theorem c1329920 : checkChunk 1329920 128 = true := by decide +kernel
private theorem c1330048 : checkChunk 1330048 128 = true := by decide +kernel
private theorem c1330176 : checkChunk 1330176 128 = true := by decide +kernel
private theorem c1330304 : checkChunk 1330304 128 = true := by decide +kernel
private theorem c1330432 : checkChunk 1330432 128 = true := by decide +kernel
private theorem c1330560 : checkChunk 1330560 128 = true := by decide +kernel
private theorem c1330688 : checkChunk 1330688 128 = true := by decide +kernel
private theorem c1330816 : checkChunk 1330816 128 = true := by decide +kernel
private theorem c1330944 : checkChunk 1330944 128 = true := by decide +kernel
private theorem c1331072 : checkChunk 1331072 128 = true := by decide +kernel
private theorem c1331200 : checkChunk 1331200 128 = true := by decide +kernel
private theorem c1331328 : checkChunk 1331328 128 = true := by decide +kernel
private theorem c1331456 : checkChunk 1331456 128 = true := by decide +kernel
private theorem c1331584 : checkChunk 1331584 128 = true := by decide +kernel
private theorem c1331712 : checkChunk 1331712 128 = true := by decide +kernel
private theorem c1331840 : checkChunk 1331840 128 = true := by decide +kernel
private theorem c1331968 : checkChunk 1331968 128 = true := by decide +kernel
private theorem c1332096 : checkChunk 1332096 128 = true := by decide +kernel
private theorem c1332224 : checkChunk 1332224 128 = true := by decide +kernel
private theorem c1332352 : checkChunk 1332352 128 = true := by decide +kernel
private theorem c1332480 : checkChunk 1332480 128 = true := by decide +kernel
private theorem c1332608 : checkChunk 1332608 128 = true := by decide +kernel
private theorem c1332736 : checkChunk 1332736 128 = true := by decide +kernel
private theorem c1332864 : checkChunk 1332864 128 = true := by decide +kernel
private theorem c1332992 : checkChunk 1332992 128 = true := by decide +kernel
private theorem c1333120 : checkChunk 1333120 128 = true := by decide +kernel
private theorem c1333248 : checkChunk 1333248 128 = true := by decide +kernel
private theorem c1333376 : checkChunk 1333376 128 = true := by decide +kernel
private theorem c1333504 : checkChunk 1333504 128 = true := by decide +kernel
private theorem c1333632 : checkChunk 1333632 128 = true := by decide +kernel
private theorem c1333760 : checkChunk 1333760 128 = true := by decide +kernel
private theorem c1333888 : checkChunk 1333888 128 = true := by decide +kernel
private theorem c1334016 : checkChunk 1334016 128 = true := by decide +kernel
private theorem c1334144 : checkChunk 1334144 128 = true := by decide +kernel
private theorem c1334272 : checkChunk 1334272 128 = true := by decide +kernel
private theorem c1334400 : checkChunk 1334400 128 = true := by decide +kernel
private theorem c1334528 : checkChunk 1334528 128 = true := by decide +kernel
private theorem c1334656 : checkChunk 1334656 128 = true := by decide +kernel
private theorem c1334784 : checkChunk 1334784 128 = true := by decide +kernel
private theorem c1334912 : checkChunk 1334912 128 = true := by decide +kernel
private theorem c1335040 : checkChunk 1335040 128 = true := by decide +kernel
private theorem c1335168 : checkChunk 1335168 128 = true := by decide +kernel

public theorem checked : Checked 1327104 1335296 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1327104 128 c1327104) (checkChunk_sound 1327232 128 c1327232)) (Checked.append (checkChunk_sound 1327360 128 c1327360) (checkChunk_sound 1327488 128 c1327488))) (Checked.append (Checked.append (checkChunk_sound 1327616 128 c1327616) (checkChunk_sound 1327744 128 c1327744)) (Checked.append (checkChunk_sound 1327872 128 c1327872) (checkChunk_sound 1328000 128 c1328000)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1328128 128 c1328128) (checkChunk_sound 1328256 128 c1328256)) (Checked.append (checkChunk_sound 1328384 128 c1328384) (checkChunk_sound 1328512 128 c1328512))) (Checked.append (Checked.append (checkChunk_sound 1328640 128 c1328640) (checkChunk_sound 1328768 128 c1328768)) (Checked.append (checkChunk_sound 1328896 128 c1328896) (checkChunk_sound 1329024 128 c1329024))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1329152 128 c1329152) (checkChunk_sound 1329280 128 c1329280)) (Checked.append (checkChunk_sound 1329408 128 c1329408) (checkChunk_sound 1329536 128 c1329536))) (Checked.append (Checked.append (checkChunk_sound 1329664 128 c1329664) (checkChunk_sound 1329792 128 c1329792)) (Checked.append (checkChunk_sound 1329920 128 c1329920) (checkChunk_sound 1330048 128 c1330048)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1330176 128 c1330176) (checkChunk_sound 1330304 128 c1330304)) (Checked.append (checkChunk_sound 1330432 128 c1330432) (checkChunk_sound 1330560 128 c1330560))) (Checked.append (Checked.append (checkChunk_sound 1330688 128 c1330688) (checkChunk_sound 1330816 128 c1330816)) (Checked.append (checkChunk_sound 1330944 128 c1330944) (checkChunk_sound 1331072 128 c1331072)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1331200 128 c1331200) (checkChunk_sound 1331328 128 c1331328)) (Checked.append (checkChunk_sound 1331456 128 c1331456) (checkChunk_sound 1331584 128 c1331584))) (Checked.append (Checked.append (checkChunk_sound 1331712 128 c1331712) (checkChunk_sound 1331840 128 c1331840)) (Checked.append (checkChunk_sound 1331968 128 c1331968) (checkChunk_sound 1332096 128 c1332096)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1332224 128 c1332224) (checkChunk_sound 1332352 128 c1332352)) (Checked.append (checkChunk_sound 1332480 128 c1332480) (checkChunk_sound 1332608 128 c1332608))) (Checked.append (Checked.append (checkChunk_sound 1332736 128 c1332736) (checkChunk_sound 1332864 128 c1332864)) (Checked.append (checkChunk_sound 1332992 128 c1332992) (checkChunk_sound 1333120 128 c1333120))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1333248 128 c1333248) (checkChunk_sound 1333376 128 c1333376)) (Checked.append (checkChunk_sound 1333504 128 c1333504) (checkChunk_sound 1333632 128 c1333632))) (Checked.append (Checked.append (checkChunk_sound 1333760 128 c1333760) (checkChunk_sound 1333888 128 c1333888)) (Checked.append (checkChunk_sound 1334016 128 c1334016) (checkChunk_sound 1334144 128 c1334144)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1334272 128 c1334272) (checkChunk_sound 1334400 128 c1334400)) (Checked.append (checkChunk_sound 1334528 128 c1334528) (checkChunk_sound 1334656 128 c1334656))) (Checked.append (Checked.append (checkChunk_sound 1334784 128 c1334784) (checkChunk_sound 1334912 128 c1334912)) (Checked.append (checkChunk_sound 1335040 128 c1335040) (checkChunk_sound 1335168 128 c1335168)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B005
