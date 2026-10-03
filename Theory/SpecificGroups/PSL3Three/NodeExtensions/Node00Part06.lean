module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Data
/-!
# Kernel checks for node 0, rows 3072–3583

This chunk verifies the exact-extension witnesses against the certified coset
matrices. The interval theorem joins the kernel-checked batches for assembly.
Source: `NodeExtensions.Check.sound` and `SubgroupEnumeration.ExtensionWords.sound`.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions00
open CosetCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
private theorem checked192 : checkRange rowCheck 3072 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked193 : checkRange rowCheck 3088 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked194 : checkRange rowCheck 3104 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked195 : checkRange rowCheck 3120 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked196 : checkRange rowCheck 3136 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked197 : checkRange rowCheck 3152 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked198 : checkRange rowCheck 3168 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked199 : checkRange rowCheck 3184 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked200 : checkRange rowCheck 3200 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked201 : checkRange rowCheck 3216 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked202 : checkRange rowCheck 3232 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked203 : checkRange rowCheck 3248 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked204 : checkRange rowCheck 3264 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked205 : checkRange rowCheck 3280 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked206 : checkRange rowCheck 3296 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked207 : checkRange rowCheck 3312 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked208 : checkRange rowCheck 3328 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked209 : checkRange rowCheck 3344 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked210 : checkRange rowCheck 3360 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked211 : checkRange rowCheck 3376 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked212 : checkRange rowCheck 3392 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked213 : checkRange rowCheck 3408 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked214 : checkRange rowCheck 3424 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked215 : checkRange rowCheck 3440 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked216 : checkRange rowCheck 3456 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked217 : checkRange rowCheck 3472 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked218 : checkRange rowCheck 3488 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked219 : checkRange rowCheck 3504 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked220 : checkRange rowCheck 3520 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked221 : checkRange rowCheck 3536 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked222 : checkRange rowCheck 3552 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked223 : checkRange rowCheck 3568 16 = true := by decide +kernel
public theorem checkedPart6 : checkRange rowCheck 3072 512 = true :=
  (@checkRange_append rowCheck 3072 256 256 (@checkRange_append rowCheck 3072 128 128 (@checkRange_append rowCheck 3072 64 64 (@checkRange_append rowCheck 3072 32 32 (@checkRange_append rowCheck 3072 16 16 checked192 checked193) (@checkRange_append rowCheck 3104 16 16 checked194 checked195)) (@checkRange_append rowCheck 3136 32 32 (@checkRange_append rowCheck 3136 16 16 checked196 checked197) (@checkRange_append rowCheck 3168 16 16 checked198 checked199))) (@checkRange_append rowCheck 3200 64 64 (@checkRange_append rowCheck 3200 32 32 (@checkRange_append rowCheck 3200 16 16 checked200 checked201) (@checkRange_append rowCheck 3232 16 16 checked202 checked203)) (@checkRange_append rowCheck 3264 32 32 (@checkRange_append rowCheck 3264 16 16 checked204 checked205) (@checkRange_append rowCheck 3296 16 16 checked206 checked207)))) (@checkRange_append rowCheck 3328 128 128 (@checkRange_append rowCheck 3328 64 64 (@checkRange_append rowCheck 3328 32 32 (@checkRange_append rowCheck 3328 16 16 checked208 checked209) (@checkRange_append rowCheck 3360 16 16 checked210 checked211)) (@checkRange_append rowCheck 3392 32 32 (@checkRange_append rowCheck 3392 16 16 checked212 checked213) (@checkRange_append rowCheck 3424 16 16 checked214 checked215))) (@checkRange_append rowCheck 3456 64 64 (@checkRange_append rowCheck 3456 32 32 (@checkRange_append rowCheck 3456 16 16 checked216 checked217) (@checkRange_append rowCheck 3488 16 16 checked218 checked219)) (@checkRange_append rowCheck 3520 32 32 (@checkRange_append rowCheck 3520 16 16 checked220 checked221) (@checkRange_append rowCheck 3552 16 16 checked222 checked223)))))
end Matrix.PSL3Three.CertifiedEnumeration.Extensions00
