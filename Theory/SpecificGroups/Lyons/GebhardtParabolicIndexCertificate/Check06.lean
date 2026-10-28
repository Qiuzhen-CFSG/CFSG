module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Context
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.factsTable
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.instructionsTable
public import Theory.GroupTheory.CosetWordCertificateBoolean

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_196608 : checkBoolChunk context facts instructions 196608 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_200704 : checkBoolChunk context facts instructions 200704 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_204800 : checkBoolChunk context facts instructions 204800 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_208896 : checkBoolChunk context facts instructions 208896 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_212992 : checkBoolChunk context facts instructions 212992 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_217088 : checkBoolChunk context facts instructions 217088 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_221184 : checkBoolChunk context facts instructions 221184 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_225280 : checkBoolChunk context facts instructions 225280 4096 = true := by decide +kernel

end Lyons.Gebhardt.ParabolicIndexCertificate
