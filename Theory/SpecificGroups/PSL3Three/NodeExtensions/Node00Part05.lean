module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Data
/-!
# Kernel checks for node 0, rows 2560–3071

This chunk verifies the exact-extension witnesses against the certified coset
matrices. The interval theorem joins the kernel-checked batches for assembly.
Source: `NodeExtensions.Check.sound` and `SubgroupEnumeration.ExtensionWords.sound`.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions00
open CosetCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
private theorem checked160 : checkRange rowCheck 2560 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked161 : checkRange rowCheck 2576 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked162 : checkRange rowCheck 2592 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked163 : checkRange rowCheck 2608 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked164 : checkRange rowCheck 2624 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked165 : checkRange rowCheck 2640 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked166 : checkRange rowCheck 2656 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked167 : checkRange rowCheck 2672 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked168 : checkRange rowCheck 2688 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked169 : checkRange rowCheck 2704 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked170 : checkRange rowCheck 2720 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked171 : checkRange rowCheck 2736 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked172 : checkRange rowCheck 2752 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked173 : checkRange rowCheck 2768 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked174 : checkRange rowCheck 2784 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked175 : checkRange rowCheck 2800 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked176 : checkRange rowCheck 2816 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked177 : checkRange rowCheck 2832 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked178 : checkRange rowCheck 2848 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked179 : checkRange rowCheck 2864 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked180 : checkRange rowCheck 2880 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked181 : checkRange rowCheck 2896 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked182 : checkRange rowCheck 2912 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked183 : checkRange rowCheck 2928 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked184 : checkRange rowCheck 2944 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked185 : checkRange rowCheck 2960 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked186 : checkRange rowCheck 2976 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked187 : checkRange rowCheck 2992 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked188 : checkRange rowCheck 3008 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked189 : checkRange rowCheck 3024 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked190 : checkRange rowCheck 3040 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked191 : checkRange rowCheck 3056 16 = true := by decide +kernel
public theorem checkedPart5 : checkRange rowCheck 2560 512 = true :=
  (@checkRange_append rowCheck 2560 256 256 (@checkRange_append rowCheck 2560 128 128 (@checkRange_append rowCheck 2560 64 64 (@checkRange_append rowCheck 2560 32 32 (@checkRange_append rowCheck 2560 16 16 checked160 checked161) (@checkRange_append rowCheck 2592 16 16 checked162 checked163)) (@checkRange_append rowCheck 2624 32 32 (@checkRange_append rowCheck 2624 16 16 checked164 checked165) (@checkRange_append rowCheck 2656 16 16 checked166 checked167))) (@checkRange_append rowCheck 2688 64 64 (@checkRange_append rowCheck 2688 32 32 (@checkRange_append rowCheck 2688 16 16 checked168 checked169) (@checkRange_append rowCheck 2720 16 16 checked170 checked171)) (@checkRange_append rowCheck 2752 32 32 (@checkRange_append rowCheck 2752 16 16 checked172 checked173) (@checkRange_append rowCheck 2784 16 16 checked174 checked175)))) (@checkRange_append rowCheck 2816 128 128 (@checkRange_append rowCheck 2816 64 64 (@checkRange_append rowCheck 2816 32 32 (@checkRange_append rowCheck 2816 16 16 checked176 checked177) (@checkRange_append rowCheck 2848 16 16 checked178 checked179)) (@checkRange_append rowCheck 2880 32 32 (@checkRange_append rowCheck 2880 16 16 checked180 checked181) (@checkRange_append rowCheck 2912 16 16 checked182 checked183))) (@checkRange_append rowCheck 2944 64 64 (@checkRange_append rowCheck 2944 32 32 (@checkRange_append rowCheck 2944 16 16 checked184 checked185) (@checkRange_append rowCheck 2976 16 16 checked186 checked187)) (@checkRange_append rowCheck 3008 32 32 (@checkRange_append rowCheck 3008 16 16 checked188 checked189) (@checkRange_append rowCheck 3040 16 16 checked190 checked191)))))
end Matrix.PSL3Three.CertifiedEnumeration.Extensions00
