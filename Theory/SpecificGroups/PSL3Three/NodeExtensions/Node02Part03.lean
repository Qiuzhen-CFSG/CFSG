module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node02Data
/-!
# Kernel checks for node 2, rows 1536–1871

This chunk verifies the exact-extension witnesses against the certified coset
matrices. The interval theorem joins the kernel-checked batches for assembly.
Source: `NodeExtensions.Check.sound` and `SubgroupEnumeration.ExtensionWords.sound`.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions02
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
public theorem checkedPart3 : checkRange rowCheck 1536 336 = true :=
  (@checkRange_append rowCheck 1536 160 176 (@checkRange_append rowCheck 1536 80 80 (@checkRange_append rowCheck 1536 32 48 (@checkRange_append rowCheck 1536 16 16 checked96 checked97) (@checkRange_append rowCheck 1568 16 32 checked98 (@checkRange_append rowCheck 1584 16 16 checked99 checked100))) (@checkRange_append rowCheck 1616 32 48 (@checkRange_append rowCheck 1616 16 16 checked101 checked102) (@checkRange_append rowCheck 1648 16 32 checked103 (@checkRange_append rowCheck 1664 16 16 checked104 checked105)))) (@checkRange_append rowCheck 1696 80 96 (@checkRange_append rowCheck 1696 32 48 (@checkRange_append rowCheck 1696 16 16 checked106 checked107) (@checkRange_append rowCheck 1728 16 32 checked108 (@checkRange_append rowCheck 1744 16 16 checked109 checked110))) (@checkRange_append rowCheck 1776 48 48 (@checkRange_append rowCheck 1776 16 32 checked111 (@checkRange_append rowCheck 1792 16 16 checked112 checked113)) (@checkRange_append rowCheck 1824 16 32 checked114 (@checkRange_append rowCheck 1840 16 16 checked115 checked116)))))
end Matrix.PSL3Three.CertifiedEnumeration.Extensions02
