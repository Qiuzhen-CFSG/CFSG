module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Data
/-!
# Kernel checks for node 0, rows 4608–5119

This chunk verifies the exact-extension witnesses against the certified coset
matrices. The interval theorem joins the kernel-checked batches for assembly.
Source: `NodeExtensions.Check.sound` and `SubgroupEnumeration.ExtensionWords.sound`.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions00
open CosetCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
private theorem checked288 : checkRange rowCheck 4608 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked289 : checkRange rowCheck 4624 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked290 : checkRange rowCheck 4640 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked291 : checkRange rowCheck 4656 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked292 : checkRange rowCheck 4672 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked293 : checkRange rowCheck 4688 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked294 : checkRange rowCheck 4704 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked295 : checkRange rowCheck 4720 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked296 : checkRange rowCheck 4736 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked297 : checkRange rowCheck 4752 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked298 : checkRange rowCheck 4768 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked299 : checkRange rowCheck 4784 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked300 : checkRange rowCheck 4800 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked301 : checkRange rowCheck 4816 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked302 : checkRange rowCheck 4832 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked303 : checkRange rowCheck 4848 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked304 : checkRange rowCheck 4864 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked305 : checkRange rowCheck 4880 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked306 : checkRange rowCheck 4896 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked307 : checkRange rowCheck 4912 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked308 : checkRange rowCheck 4928 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked309 : checkRange rowCheck 4944 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked310 : checkRange rowCheck 4960 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked311 : checkRange rowCheck 4976 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked312 : checkRange rowCheck 4992 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked313 : checkRange rowCheck 5008 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked314 : checkRange rowCheck 5024 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked315 : checkRange rowCheck 5040 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked316 : checkRange rowCheck 5056 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked317 : checkRange rowCheck 5072 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked318 : checkRange rowCheck 5088 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked319 : checkRange rowCheck 5104 16 = true := by decide +kernel
public theorem checkedPart9 : checkRange rowCheck 4608 512 = true :=
  (@checkRange_append rowCheck 4608 256 256 (@checkRange_append rowCheck 4608 128 128 (@checkRange_append rowCheck 4608 64 64 (@checkRange_append rowCheck 4608 32 32 (@checkRange_append rowCheck 4608 16 16 checked288 checked289) (@checkRange_append rowCheck 4640 16 16 checked290 checked291)) (@checkRange_append rowCheck 4672 32 32 (@checkRange_append rowCheck 4672 16 16 checked292 checked293) (@checkRange_append rowCheck 4704 16 16 checked294 checked295))) (@checkRange_append rowCheck 4736 64 64 (@checkRange_append rowCheck 4736 32 32 (@checkRange_append rowCheck 4736 16 16 checked296 checked297) (@checkRange_append rowCheck 4768 16 16 checked298 checked299)) (@checkRange_append rowCheck 4800 32 32 (@checkRange_append rowCheck 4800 16 16 checked300 checked301) (@checkRange_append rowCheck 4832 16 16 checked302 checked303)))) (@checkRange_append rowCheck 4864 128 128 (@checkRange_append rowCheck 4864 64 64 (@checkRange_append rowCheck 4864 32 32 (@checkRange_append rowCheck 4864 16 16 checked304 checked305) (@checkRange_append rowCheck 4896 16 16 checked306 checked307)) (@checkRange_append rowCheck 4928 32 32 (@checkRange_append rowCheck 4928 16 16 checked308 checked309) (@checkRange_append rowCheck 4960 16 16 checked310 checked311))) (@checkRange_append rowCheck 4992 64 64 (@checkRange_append rowCheck 4992 32 32 (@checkRange_append rowCheck 4992 16 16 checked312 checked313) (@checkRange_append rowCheck 5024 16 16 checked314 checked315)) (@checkRange_append rowCheck 5056 32 32 (@checkRange_append rowCheck 5056 16 16 checked316 checked317) (@checkRange_append rowCheck 5088 16 16 checked318 checked319)))))
end Matrix.PSL3Three.CertifiedEnumeration.Extensions00
