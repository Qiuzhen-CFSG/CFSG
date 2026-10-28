module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node01Data
/-!
# Kernel checks for node 1, rows 2048–2559

This chunk verifies the exact-extension witnesses against the certified coset
matrices. The interval theorem joins the kernel-checked batches for assembly.
Source: `NodeExtensions.Check.sound` and `SubgroupEnumeration.ExtensionWords.sound`.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions01
open CosetCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
private theorem checked128 : checkRange rowCheck 2048 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked129 : checkRange rowCheck 2064 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked130 : checkRange rowCheck 2080 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked131 : checkRange rowCheck 2096 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked132 : checkRange rowCheck 2112 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked133 : checkRange rowCheck 2128 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked134 : checkRange rowCheck 2144 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked135 : checkRange rowCheck 2160 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked136 : checkRange rowCheck 2176 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked137 : checkRange rowCheck 2192 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked138 : checkRange rowCheck 2208 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked139 : checkRange rowCheck 2224 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked140 : checkRange rowCheck 2240 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked141 : checkRange rowCheck 2256 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked142 : checkRange rowCheck 2272 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked143 : checkRange rowCheck 2288 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked144 : checkRange rowCheck 2304 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked145 : checkRange rowCheck 2320 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked146 : checkRange rowCheck 2336 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked147 : checkRange rowCheck 2352 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked148 : checkRange rowCheck 2368 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked149 : checkRange rowCheck 2384 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked150 : checkRange rowCheck 2400 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked151 : checkRange rowCheck 2416 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked152 : checkRange rowCheck 2432 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked153 : checkRange rowCheck 2448 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked154 : checkRange rowCheck 2464 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked155 : checkRange rowCheck 2480 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked156 : checkRange rowCheck 2496 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked157 : checkRange rowCheck 2512 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked158 : checkRange rowCheck 2528 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked159 : checkRange rowCheck 2544 16 = true := by decide +kernel
public theorem checkedPart4 : checkRange rowCheck 2048 512 = true :=
  (@checkRange_append rowCheck 2048 256 256 (@checkRange_append rowCheck 2048 128 128 (@checkRange_append rowCheck 2048 64 64 (@checkRange_append rowCheck 2048 32 32 (@checkRange_append rowCheck 2048 16 16 checked128 checked129) (@checkRange_append rowCheck 2080 16 16 checked130 checked131)) (@checkRange_append rowCheck 2112 32 32 (@checkRange_append rowCheck 2112 16 16 checked132 checked133) (@checkRange_append rowCheck 2144 16 16 checked134 checked135))) (@checkRange_append rowCheck 2176 64 64 (@checkRange_append rowCheck 2176 32 32 (@checkRange_append rowCheck 2176 16 16 checked136 checked137) (@checkRange_append rowCheck 2208 16 16 checked138 checked139)) (@checkRange_append rowCheck 2240 32 32 (@checkRange_append rowCheck 2240 16 16 checked140 checked141) (@checkRange_append rowCheck 2272 16 16 checked142 checked143)))) (@checkRange_append rowCheck 2304 128 128 (@checkRange_append rowCheck 2304 64 64 (@checkRange_append rowCheck 2304 32 32 (@checkRange_append rowCheck 2304 16 16 checked144 checked145) (@checkRange_append rowCheck 2336 16 16 checked146 checked147)) (@checkRange_append rowCheck 2368 32 32 (@checkRange_append rowCheck 2368 16 16 checked148 checked149) (@checkRange_append rowCheck 2400 16 16 checked150 checked151))) (@checkRange_append rowCheck 2432 64 64 (@checkRange_append rowCheck 2432 32 32 (@checkRange_append rowCheck 2432 16 16 checked152 checked153) (@checkRange_append rowCheck 2464 16 16 checked154 checked155)) (@checkRange_append rowCheck 2496 32 32 (@checkRange_append rowCheck 2496 16 16 checked156 checked157) (@checkRange_append rowCheck 2528 16 16 checked158 checked159)))))
end Matrix.PSL3Three.CertifiedEnumeration.Extensions01
