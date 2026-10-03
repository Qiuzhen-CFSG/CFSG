module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Data
/-!
# Kernel checks for node 0, rows 3584–4095

This chunk verifies the exact-extension witnesses against the certified coset
matrices. The interval theorem joins the kernel-checked batches for assembly.
Source: `NodeExtensions.Check.sound` and `SubgroupEnumeration.ExtensionWords.sound`.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions00
open CosetCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
private theorem checked224 : checkRange rowCheck 3584 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked225 : checkRange rowCheck 3600 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked226 : checkRange rowCheck 3616 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked227 : checkRange rowCheck 3632 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked228 : checkRange rowCheck 3648 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked229 : checkRange rowCheck 3664 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked230 : checkRange rowCheck 3680 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked231 : checkRange rowCheck 3696 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked232 : checkRange rowCheck 3712 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked233 : checkRange rowCheck 3728 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked234 : checkRange rowCheck 3744 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked235 : checkRange rowCheck 3760 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked236 : checkRange rowCheck 3776 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked237 : checkRange rowCheck 3792 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked238 : checkRange rowCheck 3808 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked239 : checkRange rowCheck 3824 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked240 : checkRange rowCheck 3840 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked241 : checkRange rowCheck 3856 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked242 : checkRange rowCheck 3872 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked243 : checkRange rowCheck 3888 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked244 : checkRange rowCheck 3904 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked245 : checkRange rowCheck 3920 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked246 : checkRange rowCheck 3936 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked247 : checkRange rowCheck 3952 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked248 : checkRange rowCheck 3968 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked249 : checkRange rowCheck 3984 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked250 : checkRange rowCheck 4000 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked251 : checkRange rowCheck 4016 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked252 : checkRange rowCheck 4032 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked253 : checkRange rowCheck 4048 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked254 : checkRange rowCheck 4064 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked255 : checkRange rowCheck 4080 16 = true := by decide +kernel
public theorem checkedPart7 : checkRange rowCheck 3584 512 = true :=
  (@checkRange_append rowCheck 3584 256 256 (@checkRange_append rowCheck 3584 128 128 (@checkRange_append rowCheck 3584 64 64 (@checkRange_append rowCheck 3584 32 32 (@checkRange_append rowCheck 3584 16 16 checked224 checked225) (@checkRange_append rowCheck 3616 16 16 checked226 checked227)) (@checkRange_append rowCheck 3648 32 32 (@checkRange_append rowCheck 3648 16 16 checked228 checked229) (@checkRange_append rowCheck 3680 16 16 checked230 checked231))) (@checkRange_append rowCheck 3712 64 64 (@checkRange_append rowCheck 3712 32 32 (@checkRange_append rowCheck 3712 16 16 checked232 checked233) (@checkRange_append rowCheck 3744 16 16 checked234 checked235)) (@checkRange_append rowCheck 3776 32 32 (@checkRange_append rowCheck 3776 16 16 checked236 checked237) (@checkRange_append rowCheck 3808 16 16 checked238 checked239)))) (@checkRange_append rowCheck 3840 128 128 (@checkRange_append rowCheck 3840 64 64 (@checkRange_append rowCheck 3840 32 32 (@checkRange_append rowCheck 3840 16 16 checked240 checked241) (@checkRange_append rowCheck 3872 16 16 checked242 checked243)) (@checkRange_append rowCheck 3904 32 32 (@checkRange_append rowCheck 3904 16 16 checked244 checked245) (@checkRange_append rowCheck 3936 16 16 checked246 checked247))) (@checkRange_append rowCheck 3968 64 64 (@checkRange_append rowCheck 3968 32 32 (@checkRange_append rowCheck 3968 16 16 checked248 checked249) (@checkRange_append rowCheck 4000 16 16 checked250 checked251)) (@checkRange_append rowCheck 4032 32 32 (@checkRange_append rowCheck 4032 16 16 checked252 checked253) (@checkRange_append rowCheck 4064 16 16 checked254 checked255)))))
end Matrix.PSL3Three.CertifiedEnumeration.Extensions00
