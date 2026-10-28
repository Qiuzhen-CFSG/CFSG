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
theorem checked_163840 : checkBoolChunk context facts instructions 163840 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_167936 : checkBoolChunk context facts instructions 167936 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_172032 : checkBoolChunk context facts instructions 172032 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_176128 : checkBoolChunk context facts instructions 176128 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_180224 : checkBoolChunk context facts instructions 180224 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_184320 : checkBoolChunk context facts instructions 184320 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_188416 : checkBoolChunk context facts instructions 188416 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_192512 : checkBoolChunk context facts instructions 192512 4096 = true := by decide +kernel

end Lyons.Gebhardt.ParabolicIndexCertificate
