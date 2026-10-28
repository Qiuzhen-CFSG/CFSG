module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node05Data
/-!
# Kernel checks for node 5, rows 1024–1403

This chunk verifies the exact-extension witnesses against the certified coset
matrices. The interval theorem joins the kernel-checked batches for assembly.
Source: `NodeExtensions.Check.sound` and `SubgroupEnumeration.ExtensionWords.sound`.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions05
open CosetCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
private theorem checked64 : checkRange rowCheck 1024 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked65 : checkRange rowCheck 1040 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked66 : checkRange rowCheck 1056 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked67 : checkRange rowCheck 1072 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked68 : checkRange rowCheck 1088 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked69 : checkRange rowCheck 1104 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked70 : checkRange rowCheck 1120 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked71 : checkRange rowCheck 1136 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked72 : checkRange rowCheck 1152 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked73 : checkRange rowCheck 1168 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked74 : checkRange rowCheck 1184 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked75 : checkRange rowCheck 1200 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked76 : checkRange rowCheck 1216 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked77 : checkRange rowCheck 1232 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked78 : checkRange rowCheck 1248 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked79 : checkRange rowCheck 1264 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked80 : checkRange rowCheck 1280 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked81 : checkRange rowCheck 1296 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked82 : checkRange rowCheck 1312 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked83 : checkRange rowCheck 1328 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked84 : checkRange rowCheck 1344 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked85 : checkRange rowCheck 1360 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked86 : checkRange rowCheck 1376 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked87 : checkRange rowCheck 1392 12 = true := by decide +kernel
public theorem checkedPart2 : checkRange rowCheck 1024 380 = true :=
  (@checkRange_append rowCheck 1024 192 188 (@checkRange_append rowCheck 1024 96 96 (@checkRange_append rowCheck 1024 48 48 (@checkRange_append rowCheck 1024 16 32 checked64 (@checkRange_append rowCheck 1040 16 16 checked65 checked66)) (@checkRange_append rowCheck 1072 16 32 checked67 (@checkRange_append rowCheck 1088 16 16 checked68 checked69))) (@checkRange_append rowCheck 1120 48 48 (@checkRange_append rowCheck 1120 16 32 checked70 (@checkRange_append rowCheck 1136 16 16 checked71 checked72)) (@checkRange_append rowCheck 1168 16 32 checked73 (@checkRange_append rowCheck 1184 16 16 checked74 checked75)))) (@checkRange_append rowCheck 1216 96 92 (@checkRange_append rowCheck 1216 48 48 (@checkRange_append rowCheck 1216 16 32 checked76 (@checkRange_append rowCheck 1232 16 16 checked77 checked78)) (@checkRange_append rowCheck 1264 16 32 checked79 (@checkRange_append rowCheck 1280 16 16 checked80 checked81))) (@checkRange_append rowCheck 1312 48 44 (@checkRange_append rowCheck 1312 16 32 checked82 (@checkRange_append rowCheck 1328 16 16 checked83 checked84)) (@checkRange_append rowCheck 1360 16 28 checked85 (@checkRange_append rowCheck 1376 16 12 checked86 checked87)))))
end Matrix.PSL3Three.CertifiedEnumeration.Extensions05
