module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Data
/-!
# Kernel checks for node 0, rows 512–1023

This chunk verifies the exact-extension witnesses against the certified coset
matrices. The interval theorem joins the kernel-checked batches for assembly.
Source: `NodeExtensions.Check.sound` and `SubgroupEnumeration.ExtensionWords.sound`.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions00
open CosetCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
private theorem checked32 : checkRange rowCheck 512 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked33 : checkRange rowCheck 528 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked34 : checkRange rowCheck 544 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked35 : checkRange rowCheck 560 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked36 : checkRange rowCheck 576 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked37 : checkRange rowCheck 592 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked38 : checkRange rowCheck 608 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked39 : checkRange rowCheck 624 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked40 : checkRange rowCheck 640 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked41 : checkRange rowCheck 656 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked42 : checkRange rowCheck 672 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked43 : checkRange rowCheck 688 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked44 : checkRange rowCheck 704 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked45 : checkRange rowCheck 720 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked46 : checkRange rowCheck 736 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked47 : checkRange rowCheck 752 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked48 : checkRange rowCheck 768 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked49 : checkRange rowCheck 784 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked50 : checkRange rowCheck 800 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked51 : checkRange rowCheck 816 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked52 : checkRange rowCheck 832 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked53 : checkRange rowCheck 848 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked54 : checkRange rowCheck 864 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked55 : checkRange rowCheck 880 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked56 : checkRange rowCheck 896 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked57 : checkRange rowCheck 912 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked58 : checkRange rowCheck 928 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked59 : checkRange rowCheck 944 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked60 : checkRange rowCheck 960 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked61 : checkRange rowCheck 976 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked62 : checkRange rowCheck 992 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked63 : checkRange rowCheck 1008 16 = true := by decide +kernel
public theorem checkedPart1 : checkRange rowCheck 512 512 = true :=
  (@checkRange_append rowCheck 512 256 256 (@checkRange_append rowCheck 512 128 128 (@checkRange_append rowCheck 512 64 64 (@checkRange_append rowCheck 512 32 32 (@checkRange_append rowCheck 512 16 16 checked32 checked33) (@checkRange_append rowCheck 544 16 16 checked34 checked35)) (@checkRange_append rowCheck 576 32 32 (@checkRange_append rowCheck 576 16 16 checked36 checked37) (@checkRange_append rowCheck 608 16 16 checked38 checked39))) (@checkRange_append rowCheck 640 64 64 (@checkRange_append rowCheck 640 32 32 (@checkRange_append rowCheck 640 16 16 checked40 checked41) (@checkRange_append rowCheck 672 16 16 checked42 checked43)) (@checkRange_append rowCheck 704 32 32 (@checkRange_append rowCheck 704 16 16 checked44 checked45) (@checkRange_append rowCheck 736 16 16 checked46 checked47)))) (@checkRange_append rowCheck 768 128 128 (@checkRange_append rowCheck 768 64 64 (@checkRange_append rowCheck 768 32 32 (@checkRange_append rowCheck 768 16 16 checked48 checked49) (@checkRange_append rowCheck 800 16 16 checked50 checked51)) (@checkRange_append rowCheck 832 32 32 (@checkRange_append rowCheck 832 16 16 checked52 checked53) (@checkRange_append rowCheck 864 16 16 checked54 checked55))) (@checkRange_append rowCheck 896 64 64 (@checkRange_append rowCheck 896 32 32 (@checkRange_append rowCheck 896 16 16 checked56 checked57) (@checkRange_append rowCheck 928 16 16 checked58 checked59)) (@checkRange_append rowCheck 960 32 32 (@checkRange_append rowCheck 960 16 16 checked60 checked61) (@checkRange_append rowCheck 992 16 16 checked62 checked63)))))
end Matrix.PSL3Three.CertifiedEnumeration.Extensions00
