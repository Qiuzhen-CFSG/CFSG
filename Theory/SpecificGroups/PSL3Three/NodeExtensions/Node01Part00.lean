module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node01Data
/-!
# Kernel checks for node 1, rows 0–511

This chunk verifies the exact-extension witnesses against the certified coset
matrices. The interval theorem joins the kernel-checked batches for assembly.
Source: `NodeExtensions.Check.sound` and `SubgroupEnumeration.ExtensionWords.sound`.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions01
open CosetCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
private theorem checked0 : checkRange rowCheck 0 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked1 : checkRange rowCheck 16 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked2 : checkRange rowCheck 32 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked3 : checkRange rowCheck 48 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked4 : checkRange rowCheck 64 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked5 : checkRange rowCheck 80 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked6 : checkRange rowCheck 96 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked7 : checkRange rowCheck 112 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked8 : checkRange rowCheck 128 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked9 : checkRange rowCheck 144 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked10 : checkRange rowCheck 160 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked11 : checkRange rowCheck 176 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked12 : checkRange rowCheck 192 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked13 : checkRange rowCheck 208 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked14 : checkRange rowCheck 224 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked15 : checkRange rowCheck 240 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked16 : checkRange rowCheck 256 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked17 : checkRange rowCheck 272 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked18 : checkRange rowCheck 288 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked19 : checkRange rowCheck 304 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked20 : checkRange rowCheck 320 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked21 : checkRange rowCheck 336 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked22 : checkRange rowCheck 352 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked23 : checkRange rowCheck 368 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked24 : checkRange rowCheck 384 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked25 : checkRange rowCheck 400 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked26 : checkRange rowCheck 416 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked27 : checkRange rowCheck 432 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked28 : checkRange rowCheck 448 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked29 : checkRange rowCheck 464 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked30 : checkRange rowCheck 480 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked31 : checkRange rowCheck 496 16 = true := by decide +kernel
public theorem checkedPart0 : checkRange rowCheck 0 512 = true :=
  (@checkRange_append rowCheck 0 256 256 (@checkRange_append rowCheck 0 128 128 (@checkRange_append rowCheck 0 64 64 (@checkRange_append rowCheck 0 32 32 (@checkRange_append rowCheck 0 16 16 checked0 checked1) (@checkRange_append rowCheck 32 16 16 checked2 checked3)) (@checkRange_append rowCheck 64 32 32 (@checkRange_append rowCheck 64 16 16 checked4 checked5) (@checkRange_append rowCheck 96 16 16 checked6 checked7))) (@checkRange_append rowCheck 128 64 64 (@checkRange_append rowCheck 128 32 32 (@checkRange_append rowCheck 128 16 16 checked8 checked9) (@checkRange_append rowCheck 160 16 16 checked10 checked11)) (@checkRange_append rowCheck 192 32 32 (@checkRange_append rowCheck 192 16 16 checked12 checked13) (@checkRange_append rowCheck 224 16 16 checked14 checked15)))) (@checkRange_append rowCheck 256 128 128 (@checkRange_append rowCheck 256 64 64 (@checkRange_append rowCheck 256 32 32 (@checkRange_append rowCheck 256 16 16 checked16 checked17) (@checkRange_append rowCheck 288 16 16 checked18 checked19)) (@checkRange_append rowCheck 320 32 32 (@checkRange_append rowCheck 320 16 16 checked20 checked21) (@checkRange_append rowCheck 352 16 16 checked22 checked23))) (@checkRange_append rowCheck 384 64 64 (@checkRange_append rowCheck 384 32 32 (@checkRange_append rowCheck 384 16 16 checked24 checked25) (@checkRange_append rowCheck 416 16 16 checked26 checked27)) (@checkRange_append rowCheck 448 32 32 (@checkRange_append rowCheck 448 16 16 checked28 checked29) (@checkRange_append rowCheck 480 16 16 checked30 checked31)))))
end Matrix.PSL3Three.CertifiedEnumeration.Extensions01
