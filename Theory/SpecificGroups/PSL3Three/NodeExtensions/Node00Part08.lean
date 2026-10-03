module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Data
/-!
# Kernel checks for node 0, rows 4096–4607

This chunk verifies the exact-extension witnesses against the certified coset
matrices. The interval theorem joins the kernel-checked batches for assembly.
Source: `NodeExtensions.Check.sound` and `SubgroupEnumeration.ExtensionWords.sound`.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions00
open CosetCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
private theorem checked256 : checkRange rowCheck 4096 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked257 : checkRange rowCheck 4112 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked258 : checkRange rowCheck 4128 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked259 : checkRange rowCheck 4144 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked260 : checkRange rowCheck 4160 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked261 : checkRange rowCheck 4176 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked262 : checkRange rowCheck 4192 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked263 : checkRange rowCheck 4208 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked264 : checkRange rowCheck 4224 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked265 : checkRange rowCheck 4240 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked266 : checkRange rowCheck 4256 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked267 : checkRange rowCheck 4272 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked268 : checkRange rowCheck 4288 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked269 : checkRange rowCheck 4304 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked270 : checkRange rowCheck 4320 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked271 : checkRange rowCheck 4336 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked272 : checkRange rowCheck 4352 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked273 : checkRange rowCheck 4368 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked274 : checkRange rowCheck 4384 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked275 : checkRange rowCheck 4400 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked276 : checkRange rowCheck 4416 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked277 : checkRange rowCheck 4432 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked278 : checkRange rowCheck 4448 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked279 : checkRange rowCheck 4464 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked280 : checkRange rowCheck 4480 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked281 : checkRange rowCheck 4496 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked282 : checkRange rowCheck 4512 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked283 : checkRange rowCheck 4528 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked284 : checkRange rowCheck 4544 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked285 : checkRange rowCheck 4560 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked286 : checkRange rowCheck 4576 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked287 : checkRange rowCheck 4592 16 = true := by decide +kernel
public theorem checkedPart8 : checkRange rowCheck 4096 512 = true :=
  (@checkRange_append rowCheck 4096 256 256 (@checkRange_append rowCheck 4096 128 128 (@checkRange_append rowCheck 4096 64 64 (@checkRange_append rowCheck 4096 32 32 (@checkRange_append rowCheck 4096 16 16 checked256 checked257) (@checkRange_append rowCheck 4128 16 16 checked258 checked259)) (@checkRange_append rowCheck 4160 32 32 (@checkRange_append rowCheck 4160 16 16 checked260 checked261) (@checkRange_append rowCheck 4192 16 16 checked262 checked263))) (@checkRange_append rowCheck 4224 64 64 (@checkRange_append rowCheck 4224 32 32 (@checkRange_append rowCheck 4224 16 16 checked264 checked265) (@checkRange_append rowCheck 4256 16 16 checked266 checked267)) (@checkRange_append rowCheck 4288 32 32 (@checkRange_append rowCheck 4288 16 16 checked268 checked269) (@checkRange_append rowCheck 4320 16 16 checked270 checked271)))) (@checkRange_append rowCheck 4352 128 128 (@checkRange_append rowCheck 4352 64 64 (@checkRange_append rowCheck 4352 32 32 (@checkRange_append rowCheck 4352 16 16 checked272 checked273) (@checkRange_append rowCheck 4384 16 16 checked274 checked275)) (@checkRange_append rowCheck 4416 32 32 (@checkRange_append rowCheck 4416 16 16 checked276 checked277) (@checkRange_append rowCheck 4448 16 16 checked278 checked279))) (@checkRange_append rowCheck 4480 64 64 (@checkRange_append rowCheck 4480 32 32 (@checkRange_append rowCheck 4480 16 16 checked280 checked281) (@checkRange_append rowCheck 4512 16 16 checked282 checked283)) (@checkRange_append rowCheck 4544 32 32 (@checkRange_append rowCheck 4544 16 16 checked284 checked285) (@checkRange_append rowCheck 4576 16 16 checked286 checked287)))))
end Matrix.PSL3Three.CertifiedEnumeration.Extensions00
