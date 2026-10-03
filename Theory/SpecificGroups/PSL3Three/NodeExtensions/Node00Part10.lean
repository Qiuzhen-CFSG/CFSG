module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Data
/-!
# Kernel checks for node 0, rows 5120–5615

This chunk verifies the exact-extension witnesses against the certified coset
matrices. The interval theorem joins the kernel-checked batches for assembly.
Source: `NodeExtensions.Check.sound` and `SubgroupEnumeration.ExtensionWords.sound`.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions00
open CosetCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
private theorem checked320 : checkRange rowCheck 5120 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked321 : checkRange rowCheck 5136 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked322 : checkRange rowCheck 5152 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked323 : checkRange rowCheck 5168 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked324 : checkRange rowCheck 5184 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked325 : checkRange rowCheck 5200 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked326 : checkRange rowCheck 5216 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked327 : checkRange rowCheck 5232 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked328 : checkRange rowCheck 5248 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked329 : checkRange rowCheck 5264 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked330 : checkRange rowCheck 5280 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked331 : checkRange rowCheck 5296 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked332 : checkRange rowCheck 5312 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked333 : checkRange rowCheck 5328 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked334 : checkRange rowCheck 5344 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked335 : checkRange rowCheck 5360 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked336 : checkRange rowCheck 5376 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked337 : checkRange rowCheck 5392 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked338 : checkRange rowCheck 5408 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked339 : checkRange rowCheck 5424 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked340 : checkRange rowCheck 5440 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked341 : checkRange rowCheck 5456 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked342 : checkRange rowCheck 5472 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked343 : checkRange rowCheck 5488 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked344 : checkRange rowCheck 5504 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked345 : checkRange rowCheck 5520 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked346 : checkRange rowCheck 5536 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked347 : checkRange rowCheck 5552 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked348 : checkRange rowCheck 5568 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked349 : checkRange rowCheck 5584 16 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private theorem checked350 : checkRange rowCheck 5600 16 = true := by decide +kernel
public theorem checkedPart10 : checkRange rowCheck 5120 496 = true :=
  (@checkRange_append rowCheck 5120 240 256 (@checkRange_append rowCheck 5120 112 128 (@checkRange_append rowCheck 5120 48 64 (@checkRange_append rowCheck 5120 16 32 checked320 (@checkRange_append rowCheck 5136 16 16 checked321 checked322)) (@checkRange_append rowCheck 5168 32 32 (@checkRange_append rowCheck 5168 16 16 checked323 checked324) (@checkRange_append rowCheck 5200 16 16 checked325 checked326))) (@checkRange_append rowCheck 5232 64 64 (@checkRange_append rowCheck 5232 32 32 (@checkRange_append rowCheck 5232 16 16 checked327 checked328) (@checkRange_append rowCheck 5264 16 16 checked329 checked330)) (@checkRange_append rowCheck 5296 32 32 (@checkRange_append rowCheck 5296 16 16 checked331 checked332) (@checkRange_append rowCheck 5328 16 16 checked333 checked334)))) (@checkRange_append rowCheck 5360 128 128 (@checkRange_append rowCheck 5360 64 64 (@checkRange_append rowCheck 5360 32 32 (@checkRange_append rowCheck 5360 16 16 checked335 checked336) (@checkRange_append rowCheck 5392 16 16 checked337 checked338)) (@checkRange_append rowCheck 5424 32 32 (@checkRange_append rowCheck 5424 16 16 checked339 checked340) (@checkRange_append rowCheck 5456 16 16 checked341 checked342))) (@checkRange_append rowCheck 5488 64 64 (@checkRange_append rowCheck 5488 32 32 (@checkRange_append rowCheck 5488 16 16 checked343 checked344) (@checkRange_append rowCheck 5520 16 16 checked345 checked346)) (@checkRange_append rowCheck 5552 32 32 (@checkRange_append rowCheck 5552 16 16 checked347 checked348) (@checkRange_append rowCheck 5584 16 16 checked349 checked350)))))
end Matrix.PSL3Three.CertifiedEnumeration.Extensions00
