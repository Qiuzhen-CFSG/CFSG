module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_131072 : Scan.checkChunk context facts instructions 131072 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_132096 : Scan.checkChunk context facts instructions 132096 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_133120 : Scan.checkChunk context facts instructions 133120 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_134144 : Scan.checkChunk context facts instructions 134144 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_135168 : Scan.checkChunk context facts instructions 135168 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_136192 : Scan.checkChunk context facts instructions 136192 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_137216 : Scan.checkChunk context facts instructions 137216 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_138240 : Scan.checkChunk context facts instructions 138240 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_139264 : Scan.checkChunk context facts instructions 139264 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_140288 : Scan.checkChunk context facts instructions 140288 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_141312 : Scan.checkChunk context facts instructions 141312 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_142336 : Scan.checkChunk context facts instructions 142336 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_143360 : Scan.checkChunk context facts instructions 143360 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_144384 : Scan.checkChunk context facts instructions 144384 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_145408 : Scan.checkChunk context facts instructions 145408 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_146432 : Scan.checkChunk context facts instructions 146432 1024 = true := by
  decide +kernel

theorem sound_131072 (prior : ∀ n, n < 131072 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 147456 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h132096 := Scan.chunk_sound context_valid facts instructions 131072 1024
    prior checked_131072
  have h133120 := Scan.chunk_sound context_valid facts instructions 132096 1024
    h132096 checked_132096
  have h134144 := Scan.chunk_sound context_valid facts instructions 133120 1024
    h133120 checked_133120
  have h135168 := Scan.chunk_sound context_valid facts instructions 134144 1024
    h134144 checked_134144
  have h136192 := Scan.chunk_sound context_valid facts instructions 135168 1024
    h135168 checked_135168
  have h137216 := Scan.chunk_sound context_valid facts instructions 136192 1024
    h136192 checked_136192
  have h138240 := Scan.chunk_sound context_valid facts instructions 137216 1024
    h137216 checked_137216
  have h139264 := Scan.chunk_sound context_valid facts instructions 138240 1024
    h138240 checked_138240
  have h140288 := Scan.chunk_sound context_valid facts instructions 139264 1024
    h139264 checked_139264
  have h141312 := Scan.chunk_sound context_valid facts instructions 140288 1024
    h140288 checked_140288
  have h142336 := Scan.chunk_sound context_valid facts instructions 141312 1024
    h141312 checked_141312
  have h143360 := Scan.chunk_sound context_valid facts instructions 142336 1024
    h142336 checked_142336
  have h144384 := Scan.chunk_sound context_valid facts instructions 143360 1024
    h143360 checked_143360
  have h145408 := Scan.chunk_sound context_valid facts instructions 144384 1024
    h144384 checked_144384
  have h146432 := Scan.chunk_sound context_valid facts instructions 145408 1024
    h145408 checked_145408
  have h147456 := Scan.chunk_sound context_valid facts instructions 146432 1024
    h146432 checked_146432
  exact h147456

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
