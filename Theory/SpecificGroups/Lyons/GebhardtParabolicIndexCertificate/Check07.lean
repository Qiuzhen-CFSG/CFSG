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
theorem checked_229376 : checkBoolChunk context facts instructions 229376 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_233472 : checkBoolChunk context facts instructions 233472 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_237568 : checkBoolChunk context facts instructions 237568 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_241664 : checkBoolChunk context facts instructions 241664 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_245760 : checkBoolChunk context facts instructions 245760 3418 = true := by decide +kernel

end Lyons.Gebhardt.ParabolicIndexCertificate
