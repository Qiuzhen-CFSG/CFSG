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
theorem checked_0 : checkBoolChunk context facts instructions 0 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_4096 : checkBoolChunk context facts instructions 4096 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_8192 : checkBoolChunk context facts instructions 8192 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_12288 : checkBoolChunk context facts instructions 12288 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_16384 : checkBoolChunk context facts instructions 16384 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_20480 : checkBoolChunk context facts instructions 20480 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_24576 : checkBoolChunk context facts instructions 24576 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_28672 : checkBoolChunk context facts instructions 28672 4096 = true := by decide +kernel

end Lyons.Gebhardt.ParabolicIndexCertificate
