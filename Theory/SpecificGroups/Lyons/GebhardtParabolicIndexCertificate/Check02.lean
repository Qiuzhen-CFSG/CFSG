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
theorem checked_65536 : checkBoolChunk context facts instructions 65536 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_69632 : checkBoolChunk context facts instructions 69632 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_73728 : checkBoolChunk context facts instructions 73728 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_77824 : checkBoolChunk context facts instructions 77824 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_81920 : checkBoolChunk context facts instructions 81920 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_86016 : checkBoolChunk context facts instructions 86016 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_90112 : checkBoolChunk context facts instructions 90112 4096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_94208 : checkBoolChunk context facts instructions 94208 4096 = true := by decide +kernel

end Lyons.Gebhardt.ParabolicIndexCertificate
