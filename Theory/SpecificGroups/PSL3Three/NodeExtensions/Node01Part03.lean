module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node01Data
/-!
# Kernel checks for node 1, rows 1536–2047

This chunk verifies the exact-extension witnesses against the certified coset
matrices. The interval theorem joins the kernel-checked batches for assembly.
Source: `NodeExtensions.Check.sound` and `SubgroupEnumeration.ExtensionWords.sound`.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions01
open CosetCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
private theorem checked96 : checkRange rowCheck 1536 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked97 : checkRange rowCheck 1552 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked98 : checkRange rowCheck 1568 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked99 : checkRange rowCheck 1584 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked100 : checkRange rowCheck 1600 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked101 : checkRange rowCheck 1616 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked102 : checkRange rowCheck 1632 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked103 : checkRange rowCheck 1648 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked104 : checkRange rowCheck 1664 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked105 : checkRange rowCheck 1680 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked106 : checkRange rowCheck 1696 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked107 : checkRange rowCheck 1712 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked108 : checkRange rowCheck 1728 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked109 : checkRange rowCheck 1744 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked110 : checkRange rowCheck 1760 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked111 : checkRange rowCheck 1776 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked112 : checkRange rowCheck 1792 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked113 : checkRange rowCheck 1808 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked114 : checkRange rowCheck 1824 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked115 : checkRange rowCheck 1840 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked116 : checkRange rowCheck 1856 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked117 : checkRange rowCheck 1872 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked118 : checkRange rowCheck 1888 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked119 : checkRange rowCheck 1904 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked120 : checkRange rowCheck 1920 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked121 : checkRange rowCheck 1936 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked122 : checkRange rowCheck 1952 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked123 : checkRange rowCheck 1968 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked124 : checkRange rowCheck 1984 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked125 : checkRange rowCheck 2000 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked126 : checkRange rowCheck 2016 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked127 : checkRange rowCheck 2032 16 = true := by decide +kernel
public theorem checkedPart3 : checkRange rowCheck 1536 512 = true :=
  (@checkRange_append rowCheck 1536 256 256 (@checkRange_append rowCheck 1536 128 128 (@checkRange_append rowCheck 1536 64 64 (@checkRange_append rowCheck 1536 32 32 (@checkRange_append rowCheck 1536 16 16 checked96 checked97) (@checkRange_append rowCheck 1568 16 16 checked98 checked99)) (@checkRange_append rowCheck 1600 32 32 (@checkRange_append rowCheck 1600 16 16 checked100 checked101) (@checkRange_append rowCheck 1632 16 16 checked102 checked103))) (@checkRange_append rowCheck 1664 64 64 (@checkRange_append rowCheck 1664 32 32 (@checkRange_append rowCheck 1664 16 16 checked104 checked105) (@checkRange_append rowCheck 1696 16 16 checked106 checked107)) (@checkRange_append rowCheck 1728 32 32 (@checkRange_append rowCheck 1728 16 16 checked108 checked109) (@checkRange_append rowCheck 1760 16 16 checked110 checked111)))) (@checkRange_append rowCheck 1792 128 128 (@checkRange_append rowCheck 1792 64 64 (@checkRange_append rowCheck 1792 32 32 (@checkRange_append rowCheck 1792 16 16 checked112 checked113) (@checkRange_append rowCheck 1824 16 16 checked114 checked115)) (@checkRange_append rowCheck 1856 32 32 (@checkRange_append rowCheck 1856 16 16 checked116 checked117) (@checkRange_append rowCheck 1888 16 16 checked118 checked119))) (@checkRange_append rowCheck 1920 64 64 (@checkRange_append rowCheck 1920 32 32 (@checkRange_append rowCheck 1920 16 16 checked120 checked121) (@checkRange_append rowCheck 1952 16 16 checked122 checked123)) (@checkRange_append rowCheck 1984 32 32 (@checkRange_append rowCheck 1984 16 16 checked124 checked125) (@checkRange_append rowCheck 2016 16 16 checked126 checked127)))))
end Matrix.PSL3Three.CertifiedEnumeration.Extensions01
