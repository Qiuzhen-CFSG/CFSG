module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Data
/-!
# Kernel checks for node 0, rows 1024–1535

This chunk verifies the exact-extension witnesses against the certified coset
matrices. The interval theorem joins the kernel-checked batches for assembly.
Source: `NodeExtensions.Check.sound` and `SubgroupEnumeration.ExtensionWords.sound`.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions00
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
private theorem checked87 : checkRange rowCheck 1392 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked88 : checkRange rowCheck 1408 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked89 : checkRange rowCheck 1424 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked90 : checkRange rowCheck 1440 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked91 : checkRange rowCheck 1456 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked92 : checkRange rowCheck 1472 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked93 : checkRange rowCheck 1488 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked94 : checkRange rowCheck 1504 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked95 : checkRange rowCheck 1520 16 = true := by decide +kernel
public theorem checkedPart2 : checkRange rowCheck 1024 512 = true :=
  (@checkRange_append rowCheck 1024 256 256 (@checkRange_append rowCheck 1024 128 128 (@checkRange_append rowCheck 1024 64 64 (@checkRange_append rowCheck 1024 32 32 (@checkRange_append rowCheck 1024 16 16 checked64 checked65) (@checkRange_append rowCheck 1056 16 16 checked66 checked67)) (@checkRange_append rowCheck 1088 32 32 (@checkRange_append rowCheck 1088 16 16 checked68 checked69) (@checkRange_append rowCheck 1120 16 16 checked70 checked71))) (@checkRange_append rowCheck 1152 64 64 (@checkRange_append rowCheck 1152 32 32 (@checkRange_append rowCheck 1152 16 16 checked72 checked73) (@checkRange_append rowCheck 1184 16 16 checked74 checked75)) (@checkRange_append rowCheck 1216 32 32 (@checkRange_append rowCheck 1216 16 16 checked76 checked77) (@checkRange_append rowCheck 1248 16 16 checked78 checked79)))) (@checkRange_append rowCheck 1280 128 128 (@checkRange_append rowCheck 1280 64 64 (@checkRange_append rowCheck 1280 32 32 (@checkRange_append rowCheck 1280 16 16 checked80 checked81) (@checkRange_append rowCheck 1312 16 16 checked82 checked83)) (@checkRange_append rowCheck 1344 32 32 (@checkRange_append rowCheck 1344 16 16 checked84 checked85) (@checkRange_append rowCheck 1376 16 16 checked86 checked87))) (@checkRange_append rowCheck 1408 64 64 (@checkRange_append rowCheck 1408 32 32 (@checkRange_append rowCheck 1408 16 16 checked88 checked89) (@checkRange_append rowCheck 1440 16 16 checked90 checked91)) (@checkRange_append rowCheck 1472 32 32 (@checkRange_append rowCheck 1472 16 16 checked92 checked93) (@checkRange_append rowCheck 1504 16 16 checked94 checked95)))))
end Matrix.PSL3Three.CertifiedEnumeration.Extensions00
